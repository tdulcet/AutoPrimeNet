"""Effective runtime-path collision checks; never run live operations.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import os
import sys
from pathlib import Path
import tempfile
import unittest

from gui_config import ConfigDocument, WorkspaceError, save_configuration
from gui_controller import ControllerError, backend_request, MonitorController
from test_gui_monitor import fake_monitor_process, fixture, wait_event


class PathTests(unittest.TestCase):
	def test_case_only_role_names_follow_guest_filesystem_policy(self):
		with tempfile.TemporaryDirectory() as directory:
			insensitive = os.name == "nt" or (sys.platform == "darwin" and os.pathconf(directory, 11) != 1)
			if insensitive:
				with self.assertRaisesRegex(ControllerError, "paths conflict"):
					self.validate(directory, "results_file=WORKTODO.TXT")
			else:
				self.validate(directory, "results_file=WORKTODO.TXT")
	def test_archive_directory_is_separate_and_existing(self):
		with tempfile.TemporaryDirectory() as directory:
			(Path(directory) / "proof-archive").mkdir()
			self.validate(directory, "ProofArchiveDir=proof-archive")
			(Path(directory) / "results.txt").mkdir()
			with self.assertRaisesRegex(ControllerError, "regular file"):
				self.validate(directory, "ProofArchiveDir=results.txt")
	def validate(self, directory, extra="", config_name="prime.ini", program="mlucas=True"):
		return backend_request("validate_config", directory=directory, config_name=config_name,
			text=f"[PrimeNet]\nusername=ANONYMOUS\n{program}\n" + extra)

	def test_runtime_roles_must_not_overlap(self):
		for extra in ("results_file=worktodo.txt", "logfile=results.txt", "work_file=certwork.txt",
			"results_file=results_sent.txt", "logfile=worktodo.add", "logfile=worktodo.add.lck",
			"logfile=results.txt.lck", "work_file=certwork.add",
			"results_file=autoprimenet.log.1"):
			with self.subTest(extra=extra), tempfile.TemporaryDirectory() as directory:
				with self.assertRaisesRegex(ControllerError, "paths conflict"):
					self.validate(directory, extra)

	def test_prpll_uses_indexed_names_and_ignores_unused_overrides(self):
		with tempfile.TemporaryDirectory() as directory:
			with self.assertRaisesRegex(ControllerError, "paths conflict"):
				self.validate(directory, "NumWorkers=2\nlogfile=results-1.txt", program="prpll=True")
			self.validate(directory, "NumWorkers=2\nwork_file=unused.txt\nresults_file=unused.txt", program="prpll=True")

	def test_configuration_cannot_be_a_rotated_log_destination(self):
		with tempfile.TemporaryDirectory() as directory:
			with self.assertRaisesRegex(ControllerError, "paths conflict"):
				self.validate(directory, config_name="autoprimenet.log.5")

	def test_nonregular_runtime_files_are_refused_before_backend_startup(self):
		for name, extra in (("results.txt", ""), ("activity.log", "logfile=activity.log"), ("worktodo.add", "")):
			with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
				(Path(directory) / name).mkdir()
				with self.assertRaisesRegex(ControllerError, "regular file"):
					self.validate(directory, extra)
		if hasattr(os, "mkfifo"):
			with tempfile.TemporaryDirectory() as directory:
				os.mkfifo(Path(directory) / "activity.log")
				with self.assertRaisesRegex(ControllerError, "regular file"):
					self.validate(directory, "logfile=activity.log")

	def test_worker_paths_are_relative_to_workspace_and_log_cannot_alias_them(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "one").mkdir()
			(base / "two").mkdir()
			extra = "NumWorkers=2\nlogfile=two/results.txt\n[Worker #1]\ndirectory=one\n[Worker #2]\ndirectory=two\n"
			with self.assertRaisesRegex(ControllerError, "paths conflict"):
				self.validate(directory, extra)
			self.validate(directory, extra.replace("logfile=two/results.txt", "logfile=activity.log"))

	def test_hardlink_and_symlink_aliases_are_refused(self):
		for kind in ("hardlink", "symlink"):
			with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
				work = Path(directory) / "worktodo.txt"
				work.write_text("Test=127,70,1\n")
				log = Path(directory) / "activity.log"
				try:
					if kind == "hardlink":
						os.link(work, log)
					else:
						log.symlink_to(work)
				except OSError:
					continue  # Link creation can require Windows privileges.
				with self.assertRaisesRegex(ControllerError, "paths conflict"):
					self.validate(directory, "logfile=activity.log")

	def test_conflicting_save_preserves_original_and_never_creates_backup(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			values = document.values() | {"results_file": "worktodo.txt"}
			with self.assertRaises((ControllerError, WorkspaceError)):
				save_configuration(document, values, "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(document.path.read_bytes(), document.data)
			self.assertFalse(list(Path(directory).glob("*.bak")))

	def test_existing_conflict_refused_by_supervisor_before_cli_or_backup(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			document.path.write_text(document.text + "results_file=worktodo.txt\n")
			controller = MonitorController(process_factory=fake_monitor_process)
			try:
				controller.start(ConfigDocument(directory), operation="report_results")
				self.assertIn("paths conflict", wait_event(controller, "failed")["error"])
				wait_event(controller, "exited")
				self.assertFalse((Path(directory) / "operation.record").exists())
				self.assertFalse(list(Path(directory).glob("*.bak")))
			finally:
				if controller.active:
					controller.stop(force=True)
					wait_event(controller, "exited")
