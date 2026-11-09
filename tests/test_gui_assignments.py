"""Assignment snapshots and management tests; no live reservation changes.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import gui_assignment_backup as backup
from gui_config import ConfigDocument, WorkspaceError
from gui_controller import ControllerError, MonitorController
from gui_operations import operation_arguments
from test_gui_monitor import fake_monitor_process, fixture, wait_event


class SnapshotTests(unittest.TestCase):
	def test_exact_private_work_certification_snapshots_and_manifest(self):
		with tempfile.TemporaryDirectory() as directory:
			fixture(directory)
			base = Path(directory)
			work = b"; original\r\nTest=127,70,1\r\n"
			(base / "worktodo.txt").write_bytes(work)
			(base / "certwork.txt").write_bytes(b"Cert=1,2,131,-1,1000000\n")
			(base / "results.txt").write_text("not a work snapshot")
			folder = Path(backup.snapshot_assignments(directory, "prime.ini", "recover"))
			manifest = json.loads((folder / "manifest.json").read_text())
			self.assertEqual(manifest["operation"], "recover")
			self.assertEqual(len(manifest["files"]), 2)
			self.assertEqual((folder / "worker-1-work.bin").read_bytes(), work)
			self.assertEqual((base / "worktodo.txt").read_bytes(), work)
			self.assertEqual(manifest["files"][0]["original_path"], str((base / "worktodo.txt").resolve()))
			self.assertEqual(manifest["files"][0]["size"], len(work))
			if os.name != "nt":
				self.assertEqual(folder.stat().st_mode & 0o777, 0o700)
				for path in folder.iterdir():
					self.assertEqual(path.stat().st_mode & 0o777, 0o600)

	def test_missing_files_are_recorded_without_creating_originals(self):
		with tempfile.TemporaryDirectory() as directory:
			fixture(directory)
			folder = Path(backup.snapshot_assignments(directory, "prime.ini", "recover_all"))
			manifest = json.loads((folder / "manifest.json").read_text())
			self.assertTrue(all(not entry["present"] for entry in manifest["files"]))
			self.assertEqual({path.name for path in folder.iterdir()}, {"manifest.json"})
			self.assertFalse((Path(directory) / "worktodo.txt").exists())

	def test_multiworker_and_prpll_paths(self):
		for engine in ("mlucas", "prpll"):
			with self.subTest(engine=engine), tempfile.TemporaryDirectory() as directory:
				base = Path(directory)
				text = "[PrimeNet]\nusername=ANONYMOUS\n{}=True\nNumWorkers=2\nwork_file=custom.work\n".format(engine)
				for i in range(2):
					folder = base if engine == "prpll" else base / str(i)
					folder.mkdir(exist_ok=True)
					name = "worktodo-{}.txt".format(i) if engine == "prpll" else "custom.work"
					(folder / name).write_text("worker {}\n".format(i))
					if engine != "prpll":
						text += "[Worker #{}]\ndirectory={}\n".format(i + 1, i)
				(base / "prime.ini").write_text(text)
				folder = Path(backup.snapshot_assignments(directory, "prime.ini", "unreserve_all"))
				self.assertEqual((folder / "worker-2-work.bin").read_text(), "worker 1\n")

	def test_symlink_or_nonregular_file_refuses_snapshot(self):
		for kind in ("directory", "symlink"):
			with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
				fixture(directory)
				base = Path(directory)
				if kind == "directory":
					(base / "worktodo.txt").mkdir()
				else:
					(base / "target").write_text("preserve")
					try:
						(base / "worktodo.txt").symlink_to(base / "target")
					except OSError:
						continue
				with self.assertRaises(WorkspaceError):
					backup.snapshot_assignments(directory, "prime.ini", "recover")
				self.assertFalse(list(base.glob(".gui-assignment-backup-*")))

	def test_oversize_or_total_limit_cleans_incomplete_snapshot(self):
		for limits in (dict(MAX_SNAPSHOT_FILE=4), dict(MAX_SNAPSHOT_TOTAL=4)):
			with self.subTest(limits=limits), tempfile.TemporaryDirectory() as directory:
				fixture(directory)
				base = Path(directory)
				(base / "worktodo.txt").write_bytes(b"unchanged")
				with patch.multiple(backup, **limits), self.assertRaises(WorkspaceError):
					backup.snapshot_assignments(directory, "prime.ini", "recover")
				self.assertEqual((base / "worktodo.txt").read_bytes(), b"unchanged")
				self.assertFalse(list(base.glob(".gui-assignment-backup-*")))

	def test_concurrent_change_refuses_inconsistent_snapshot(self):
		with tempfile.TemporaryDirectory() as directory:
			fixture(directory)
			base = Path(directory)
			work = base / "worktodo.txt"
			work.write_text("before")
			read = backup._read
			def changed(path):
				result = read(path)
				if path.resolve() == work.resolve():
					work.write_text("changed externally")
				return result
			with patch.object(backup, "_read", side_effect=changed), self.assertRaisesRegex(WorkspaceError, "changed during backup"):
				backup.snapshot_assignments(directory, "prime.ini", "recover")
			self.assertEqual(work.read_text(), "changed externally")
			self.assertFalse(list(base.glob(".gui-assignment-backup-*")))


class ManagementTests(unittest.TestCase):
	def test_parameter_validation_cannot_fall_through_to_normal_cli_cycle(self):
		for parameters in ({}, {"exponent": 0}, {"exponent": True}, {"exponent": "127"}, {"exponent": 10000000000}, {"exponent": 127, "flags": "--recover"}):
			with self.subTest(parameters=parameters), self.assertRaises(ValueError):
				operation_arguments("unreserve", parameters)
		self.assertEqual(operation_arguments("unreserve", {"exponent": 127}), ("--unreserve", "127"))
		with self.assertRaises(ValueError):
			operation_arguments("recover", {"exponent": 127})
		with tempfile.TemporaryDirectory() as directory:
			with self.assertRaises(ControllerError):
				MonitorController().start(fixture(directory), parameters={"exponent": 127})

	def test_recovery_requires_registration_before_simulated_cli(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			controller = MonitorController(process_factory=fake_monitor_process)
			controller.start(document, operation="recover")
			failure = wait_event(controller, "failed")
			wait_event(controller, "exited")
			self.assertIn("registration", failure["error"])
			self.assertFalse((Path(directory) / "operation.record").exists())

	def test_recovery_and_unreservation_snapshot_before_simulated_launch(self):
		for operation in ("recover", "recover_all", "unreserve", "unreserve_all"):
			with self.subTest(operation=operation), tempfile.TemporaryDirectory() as directory:
				document = fixture(directory)
				document.path.write_text(document.text + "ComputerGUID=" + "a" * 32 + "\n")
				document = ConfigDocument(directory)
				base = Path(directory)
				work = b"Test=127,70,1\n"
				(base / "worktodo.txt").write_bytes(work)
				parameters = {"exponent": 127} if operation == "unreserve" else {}
				controller = MonitorController(process_factory=fake_monitor_process)
				controller.start(document, operation=operation, parameters=parameters)
				ready = wait_event(controller, "ready")
				self.assertEqual((Path(ready["assignment_backup"]) / "worker-1-work.bin").read_bytes(), work)
				wait_event(controller, "exited")
				self.assertEqual((base / "operation.record").read_text(), operation)
				self.assertEqual(json.loads((base / "parameters.record").read_text()), parameters)
				self.assertEqual((base / "worktodo.txt").read_bytes(), work)

	def test_missing_exponent_refuses_before_snapshot_and_cli(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			controller = MonitorController(process_factory=fake_monitor_process)
			controller.start(document, operation="unreserve", parameters={"exponent": 127})
			failure = wait_event(controller, "failed")
			wait_event(controller, "exited")
			self.assertIn("not in the current", failure["error"])
			self.assertFalse((Path(directory) / "operation.record").exists())

	def test_snapshot_failure_prevents_cli_launch(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			document.path.write_text(document.text + "ComputerGUID=" + "a" * 32 + "\n")
			document = ConfigDocument(directory)
			# A nonregular configured work file must fail before any CLI body.
			(Path(directory) / "worktodo.txt").mkdir()
			controller = MonitorController(process_factory=fake_monitor_process)
			controller.start(document, operation="recover")
			wait_event(controller, "failed")
			wait_event(controller, "exited")
			self.assertFalse((Path(directory) / "operation.record").exists())
			self.assertFalse(list(Path(directory).glob(".gui-assignment-backup-*")))

	def test_real_cli_pause_resume_changes_only_local_request_policy(self):
		with tempfile.TemporaryDirectory() as directory:
			fixture(directory)
			work = Path(directory) / "worktodo.txt"
			work.write_text("Test=127,70,1\n")
			code = "import sys,runpy,gui_backend; sys.addaudithook(gui_backend._network_guard); sys.argv=['autoprimenet.py','--workdir',sys.argv[1],'--timeout','0',sys.argv[2]]; runpy.run_path('autoprimenet.py',run_name='__main__')"
			for flag, paused in (("--no-more-work", True), ("--resume-work", False)):
				process = subprocess.run([sys.executable, "-B", "-c", code, directory, flag], capture_output=True, text=True, timeout=30)
				self.assertEqual(process.returncode, 0, process.stderr)
				config = ConfigDocument(directory).config
				self.assertEqual(config.getboolean("PrimeNet", "QuitGIMPS", fallback=False), paused)
				self.assertFalse(config.has_option("PrimeNet", "ComputerGUID"))
				self.assertEqual(work.read_text(), "Test=127,70,1\n")


if __name__ == "__main__":
	unittest.main()
