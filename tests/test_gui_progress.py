"""Offline progress fixtures, discovery boundaries and native-reader integration."""

import os
from pathlib import Path
import struct
import shutil
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import psutil

from gui_backend import _load_definitions, _read_source
from gui_progress import ENGINES, MAX_FILE_BYTES, discover_processes, identify_engine, progress_snapshot

ROOT = Path(__file__).resolve().parents[1]
P = 100003


class Process:
	pid = 1234
	def __init__(self, engine, directory):
		self.engine, self.directory = engine, directory

	def name(self):
		return self.engine

	def cwd(self):
		return self.directory

	def create_time(self):
		return 123.0


def system(*processes):
	return SimpleNamespace(process_iter=lambda: iter(processes), Process=lambda pid: next(p for p in processes if p.pid == pid),
		AccessDenied=psutil.AccessDenied, NoSuchProcess=psutil.NoSuchProcess, ZombieProcess=psutil.ZombieProcess, Error=psutil.Error)


class ProgressTests(unittest.TestCase):
	@classmethod
	def setUpClass(cls):
		path = ROOT / "autoprimenet.py"
		_, tree, boundary = _read_source(path)
		cls.namespace = _load_definitions(path, tree, boundary)

	@classmethod
	def tearDownClass(cls):
		cls.namespace["session"].close()

	def snapshot(self, engine, directory, configured=None):
		return progress_snapshot(self.namespace, configured, system(Process(engine, str(directory))))

	def fixture(self, engine, directory):
		work = directory / ("worktodo-0.txt" if engine == "PRPLL" else "worktodo.txt")
		work.write_text(f'Factor={P},60,61\n' if engine in ("mfaktc", "mfakto", "PrimePath") else f'Test={P},60,1\n')
		if engine == "Mlucas":
			(directory / f'p{P}.stat').write_text('Iter# = 10000 [ 10.00% complete] foo [ 2.000 msec/iter]\n')
		elif engine == "GpuOwl":
			(directory / 'gpuowl.log').write_text(f'{P} LL 10000 2000 us/it;\n')
		elif engine == "PRPLL":
			folder = directory / str(P)
			folder.mkdir()
			(folder / f'{P}-10000.ll').write_text(f'OWL LL 13 N=1*2^{P}-1 k=10000 time=20\n')
		elif engine == "PrMers":
			(directory / f'llunsafe_m_{P}.ckpt').write_bytes(struct.pack('=iIId', 1, P, 10000, 20))
		elif engine == "CUDALucas":
			(directory / f'c{P}').write_bytes(bytes(((P + 31) // 32) * 4) + struct.pack('=10I', P, 1024, 10001, 0, 610, 0, 0, 0, 0, 0))
		elif engine == "mfaktc":
			(directory / f'M{P}.ckp').write_text(f'M{P} 60 61 420 0.24: 100 0 0 20000 00000000\n')
		elif engine == "mfakto":
			(directory / f'M{P}.ckp').write_text(f'{P} 60 61 420 mfakto 0.16: 100 0 0 20000 00000000\n')
		elif engine == "PrimePath":
			start, end = (1 << 60) // (P << 1), (1 << 61) // (P << 1)
			(directory / f'mersenne_tf_checkpoint_M{P}.txt').write_text(f'exponent {P}\nbit_lo 60\nbit_hi 61\ncurrent_k {(start + end) // 2}\ntested 1\nelapsed_sec 20\nassignment_key fixture\ntimestamp 2026-11-03 01:00:00\n')

	def test_invalid_file_time_does_not_break_progress_display(self):
		from gui_progress_view import display_time
		self.assertEqual(display_time(10 ** 15), "Unavailable")
		self.assertNotEqual(display_time(0), "Unavailable")

	def test_native_progress_for_all_eight_engines_is_read_only(self):
		for engine in ENGINES:
			with self.subTest(engine=engine), tempfile.TemporaryDirectory() as temp:
				directory = Path(temp)
				self.fixture(engine, directory)
				before = {p: p.read_bytes() for p in directory.rglob('*') if p.is_file()}
				result = self.snapshot(engine, directory)
				self.assertEqual(len(result['rows']), 1)
				row = result['rows'][0]
				self.assertEqual(row['exponent'], str(P))
				self.assertGreater(row['percent'], 0)
				self.assertGreater(row['speed'], 0)
				self.assertGreater(row['remaining'], 0)
				self.assertIsNotNone(row['updated'])
				self.assertEqual(row['state'], 'Saved progress')
				self.assertFalse(result['network_enabled'])
				self.assertFalse(result['files_written'])
				self.assertEqual(before, {p: p.read_bytes() for p in directory.rglob('*') if p.is_file()})

	def test_missing_checkpoint_is_not_zero_percent_or_stalled(self):
		with tempfile.TemporaryDirectory() as temp:
			Path(temp, 'worktodo.txt').write_text(f'Test={P},60,1\n')
			row = self.snapshot('Mlucas', temp)['rows'][0]
			self.assertIsNone(row['percent'])
			self.assertIsNone(row['updated'])
			self.assertIsNone(row['remaining'])
			self.assertEqual(row['state'], 'No saved progress / queued')

	def test_stale_uses_progress_file_time_not_workfile(self):
		with tempfile.TemporaryDirectory() as temp:
			directory = Path(temp)
			self.fixture('Mlucas', directory)
			old = time.time() - 3600
			os.utime(directory / f'p{P}.stat', (old, old))
			row = self.snapshot('Mlucas', directory)['rows'][0]
			self.assertEqual(row['state'], 'Stale saved progress')
			self.assertEqual(row['updated'], old)

	def test_library_reads_do_not_make_old_progress_look_fresh(self):
		with tempfile.TemporaryDirectory() as temp:
			base = Path(temp)
			directory = base / 'worker'
			directory.mkdir()
			self.fixture('Mlucas', directory)
			old = time.time() - 3600
			os.utime(directory / f'p{P}.stat', (old, old))
			library = base / 'library.py'
			library.write_text('fixture')
			native = self.namespace['get_progress_assignment']
			def reader(*args):
				library.read_bytes()
				return native(*args)
			with patch.dict(self.namespace, {'get_progress_assignment': reader}):
				row = self.snapshot('Mlucas', directory)['rows'][0]
			self.assertEqual(row['updated'], old)
			self.assertEqual(row['state'], 'Stale saved progress')

	def test_multiple_programs_and_shared_directory_processes(self):
		with tempfile.TemporaryDirectory() as temp:
			directory = Path(temp)
			self.fixture('Mlucas', directory)
			first, second, third = Process('Mlucas', temp), Process('Mlucas', temp), Process('mfakto', temp)
			second.pid, third.pid = 1235, 1236
			rows = progress_snapshot(self.namespace, psutil_module=system(first, second, third))['rows']
			self.assertEqual(len(rows), 2)
			self.assertEqual(rows[0]['pids'], '1234, 1235')

	def test_custom_configured_worker_directories(self):
		with tempfile.TemporaryDirectory() as temp:
			directory = Path(temp)
			worker = directory / 'worker'
			worker.mkdir()
			self.fixture('Mlucas', worker)
			(work := worker / 'custom.work').write_bytes((worker / 'worktodo.txt').read_bytes())
			configured = {'engine': 'mlucas', 'directory': temp, 'workers': [{'number': 2, 'work_file': str(work)}]}
			row = self.snapshot('Mlucas', directory, configured)['rows'][0]
			self.assertEqual(row['worker'], '2')
			self.assertIsNotNone(row['percent'])
			row = self.snapshot('Mlucas', worker, configured)['rows'][0]
			self.assertEqual(row['work_file'], str(work))
			self.assertEqual(row['worker'], '2')

	def test_unreadable_directory_and_report_only_program_remain_visible(self):
		for engine in ('Mlucas', 'Prime95', 'CUDAPm1'):
			row = self.snapshot(engine, None)['rows'][0] if engine != 'Mlucas' else progress_snapshot(self.namespace, psutil_module=system(Process(engine, None)))['rows'][0]
			self.assertEqual(row['engine'], engine)
			self.assertNotIn('percent', row)

	def test_exited_process_and_denied_process_do_not_crash_scan(self):
		process = Process('Mlucas', '.')
		with patch.object(process, 'name', side_effect=psutil.NoSuchProcess(1234)):
			self.assertEqual(discover_processes(system(process))[0], [])
		with patch.object(process, 'name', side_effect=psutil.AccessDenied(1234)):
			self.assertEqual(discover_processes(system(process))[1], 1)
		with patch.object(process, 'cwd', side_effect=psutil.AccessDenied(1234)):
			self.assertIsNone(discover_processes(system(process))[0][0]['directory'])

	def test_executable_names_do_not_match_arbitrary_commands(self):
		for name, expected in (('PRPLL-NTT.exe', 'PRPLL'), ('Mlucas.avx512', 'Mlucas'), ('mfaktc-0.24.exe', 'mfaktc'), ('not-mlucas', None), ('python', None), ('mlucas-malware', None)):
			self.assertEqual(identify_engine(name), expected)

	def test_empty_unrecognized_and_oversized_work_files(self):
		with tempfile.TemporaryDirectory() as temp:
			path = Path(temp, 'worktodo.txt')
			for text in ('', 'unrecognized', 'x' * (MAX_FILE_BYTES + 1)):
				path.write_text(text)
				row = self.snapshot('Mlucas', temp)['rows'][0]
				self.assertNotIn('percent', row)

	def test_queued_estimates_accumulate_without_inventing_progress(self):
		with tempfile.TemporaryDirectory() as temp:
			directory = Path(temp)
			self.fixture('Mlucas', directory)
			with (directory / 'worktodo.txt').open('a') as stream:
				stream.write('Test=100019,60,1\n')
			first, queued = self.snapshot('Mlucas', directory)['rows']
			self.assertIsNone(queued['percent'])
			self.assertIsNone(queued['updated'])
			self.assertGreater(queued['remaining'], first['remaining'])
			self.assertGreater(queued['completion'], first['completion'])
			self.assertEqual(queued['queue'], 2)

	def test_nonregular_work_file_is_refused(self):
		if not hasattr(os, 'mkfifo'):
			self.skipTest('Named pipes unavailable')
		with tempfile.TemporaryDirectory() as temp:
			os.mkfifo(Path(temp, 'worktodo.txt'))
			row = self.snapshot('Mlucas', temp)['rows'][0]
			self.assertIn('unavailable', row['state'])

	def test_real_bridge_progress_operation(self):
		from gui_controller import backend_request
		result = backend_request('progress')
		self.assertIsInstance(result['rows'], list)
		self.assertIsInstance(result['notice'], str)


@unittest.skipUnless(os.environ.get("AUTOPRIMENET_GUI_DESKTOP_TESTS") == "1" and Path("/bin/sh").exists(), "Requires opt-in native process discovery and /bin/sh")
class NativeDiscoveryTests(unittest.TestCase):
	def test_real_process_is_discovered_without_selected_workspace(self):
		from gui_controller import backend_request
		with tempfile.TemporaryDirectory() as temp:
			directory = Path(temp)
			executable = directory / "Mlucas"
			# macOS /bin/sh can delegate to /bin/bash, changing process identity.
			shell = Path("/bin/bash") if Path("/bin/bash").exists() else Path("/bin/sh")
			shutil.copyfile(shell, executable)
			executable.chmod(0o700)
			if sys.platform == "darwin":
				# Copied Apple binaries retain a restricted signature and are killed.
				# Ad-hoc sign only this disposable fixture, never the system binary.
				subprocess.run(["/usr/bin/codesign", "--force", "--sign", "-", str(executable)], check=True, capture_output=True)
			(directory / "worktodo.txt").write_text(f"Test={P},60,1\n")
			(directory / f"p{P}.stat").write_text("Iter# = 10000 [ 10.00% complete] foo [ 2.000 msec/iter]\n")
			# The shell's builtin read blocks on a private pipe without spawning
			# another process or relying on a renamed multicall coreutils binary.
			process = subprocess.Popen(["Mlucas", "-c", "read fixture_line"], executable=str(executable), cwd=directory,
				stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
			try:
				result = backend_request("progress")
				if process.poll() is not None:
					self.fail("Discovery fixture exited before inspection: " + process.communicate(timeout=5)[1].strip())
				rows = [row for row in result["rows"] if str(process.pid) in row["pids"].split(", ")]
				self.assertEqual(len(rows), 1, result["notice"])
				self.assertEqual(rows[0]["engine"], "Mlucas")
				self.assertGreater(rows[0]["percent"], 0)
				self.assertIsNone(process.poll(), "Progress reading must not terminate computation")
			finally:
				process.stdin.close()
				try:
					process.wait(timeout=5)
				except subprocess.TimeoutExpired:
					process.kill()
					process.wait(timeout=5)
				finally:
					process.stderr.close()
