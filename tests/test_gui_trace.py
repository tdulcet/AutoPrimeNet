"""Private tracing tests: only disposable workspaces and simulated output.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument
from gui_controller import backend_request
from gui_monitor import StopControl, _cli_once, native_cycle
from gui_reports import read_latest_trace
from gui_trace import TraceCapture, TRUNCATED, debug_arguments, debug_level, private_trace, trace_notice


class TraceTests(unittest.TestCase):
	def document(self, directory, level=2):
		path = Path(directory) / "prime.ini"
		path.write_text(f"[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n[GUI]\nDebugLevel={level}\n")
		return ConfigDocument(directory)

	def test_level_validation_flags_and_offline_validation_never_create_trace(self):
		with tempfile.TemporaryDirectory() as directory:
			for level in range(4):
				document = self.document(directory, level)
				self.assertEqual(debug_level(document.config), level)
				self.assertEqual(debug_arguments(document.config), ["--debug"] * level)
				self.assertEqual(bool(trace_notice(document)), level >= 2)
				result = backend_request("validate_config", text=document.text, directory=directory, config_name="prime.ini")
				self.assertEqual(result["debug_level"], level)
				with private_trace(directory, min(level, 1)) as trace:
					self.assertIsNone(trace)
			self.assertEqual([p.name for p in Path(directory).iterdir()], ["prime.ini"])
			with self.assertRaises(ValueError):
				debug_level(self.document(directory, 4).config)

	def test_trace_limit_keeps_draining_and_file_is_private(self):
		with tempfile.TemporaryDirectory() as directory:
			capture = TraceCapture(directory, limit=1024)
			process = subprocess.Popen([sys.executable, "-c", "import sys; sys.stdout.buffer.write(b'x' * 1000000)"], stdout=subprocess.PIPE)
			capture.start(process.stdout)
			self.assertEqual(process.wait(timeout=5), 0)
			capture.close()
			data = capture.path.read_bytes()
			self.assertEqual(len(data), 1024)
			self.assertTrue(data.endswith(TRUNCATED))
			self.assertFalse(capture.failed)
			if os.name != "nt":
				self.assertEqual(capture.path.stat().st_mode & 0o777, 0o600)

	def test_capture_write_error_does_not_stop_pipe_drain(self):
		with tempfile.TemporaryDirectory() as directory:
			capture = TraceCapture(directory)
			output = io.BytesIO(b"private-output" * 10000)
			with patch.object(capture.stream, "write", side_effect=OSError("disk full")):
				capture.start(output)
				capture.thread.join(timeout=2)
				self.assertFalse(capture.thread.is_alive())
			capture.close()
			self.assertTrue(capture.failed)
			self.assertTrue(output.closed)

	def test_one_shot_debug_argv_and_capture_do_not_put_raw_output_on_event_channel(self):
		with tempfile.TemporaryDirectory() as directory:
			self.document(directory, 3)
			process = subprocess.Popen([sys.executable, "-c", "import sys; print('fixture-secret'); print('SMTP authentication',file=sys.stderr)"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
			with patch("gui_monitor.subprocess.Popen", return_value=process) as launch, patch("gui_monitor.emit") as emit:
				self.assertEqual(_cli_once(directory, "prime.ini", StopControl(), operation="status"), (0, False))
				self.assertEqual(launch.call_args.args[0].count("--debug"), 3)
				self.assertNotIn("fixture-secret", str(emit.call_args_list))
				self.assertEqual(emit.call_args.args[0]["event"], "trace_created")
			result = read_latest_trace(ConfigDocument(directory))
			self.assertIn("fixture-secret", result["text"])
			self.assertIn("SMTP authentication", result["text"])

	def test_native_events_remain_separate_from_captured_stderr(self):
		with tempfile.TemporaryDirectory() as directory:
			self.document(directory)
			code = "import sys; sys.stdin.buffer.readline(); print('fixture-private-trace',file=sys.stderr)"
			process = subprocess.Popen([sys.executable, "-c", code], stdin=subprocess.PIPE, stderr=subprocess.PIPE)
			with patch("gui_monitor.subprocess.Popen", return_value=process) as launch, patch("gui_monitor.emit"):
				self.assertEqual(native_cycle(directory, "prime.ini", StopControl(), 1800, "sha"), (0, False))
				self.assertNotIn("stdout", launch.call_args.kwargs)
				self.assertEqual(launch.call_args.kwargs["stderr"], subprocess.PIPE)
			self.assertIn("fixture-private-trace", read_latest_trace(ConfigDocument(directory))["text"])

	def test_reader_chooses_latest_regular_file_and_never_follows_symlinks(self):
		with tempfile.TemporaryDirectory() as directory:
			document = self.document(directory)
			old = Path(directory) / ".gui-backend-trace-old.log"
			new = Path(directory) / ".gui-backend-trace-new.log"
			old.write_text("old")
			new.write_text("new")
			os.utime(old, ns=(1, 1))
			self.assertEqual(read_latest_trace(document)["text"], "new")
			link = Path(directory) / ".gui-backend-trace-linked.log"
			try:
				link.symlink_to(document.path)
			except OSError:
				return
			self.assertEqual(read_latest_trace(document)["text"], "new")

	def test_native_and_registration_adapters_enable_original_debug_startup_offline(self):
		root = Path(__file__).resolve().parents[1]
		code = r'''
import contextlib, hashlib, io, json, sys, threading
from pathlib import Path
import gui_backend, gui_registration, gui_runtime
sys.addaudithook(gui_backend._network_guard)
path = Path(sys.argv[1]) / 'prime.ini'
seen = []
def inspect(ns, *unused):
    seen.append([ns['args'].debug, ns['logger'].level, ns['HTTPConnection'].debuglevel])
    ns['main'] = lambda: None
request = dict(protocol=1, directory=str(path.parent), config_name=path.name, interval=1800, config_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    if sys.argv[2] == 'native':
        gui_runtime.execute(request, threading.Event(), lambda event: None, inspect)
    else:
        request['operation'] = 'register_computer'
        gui_registration.execute(request, inspect)
print(json.dumps(seen))
'''
		for adapter in ("native", "registration"):
			with self.subTest(adapter=adapter), tempfile.TemporaryDirectory() as directory:
				self.document(directory, 3)
				process = subprocess.run([sys.executable, "-B", "-c", code, directory, adapter], cwd=root, capture_output=True, text=True, timeout=15)
				self.assertEqual(process.returncode, 0, process.stderr)
				self.assertEqual(json.loads(process.stdout), [[3, 0, 1]])
