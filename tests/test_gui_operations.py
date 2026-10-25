"""One-shot lifecycle and argument tests; no live server actions.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument, WorkspaceError, save_configuration
from gui_controller import ControllerError, MonitorController
from gui_monitor import StopControl, _cli_once, run_operation
from gui_operations import OPERATIONS, operation_arguments
from test_gui_monitor import fake_monitor_process, fixture, wait_event


class OperationTests(unittest.TestCase):
	def test_each_operation_runs_exactly_once_without_registration_followup(self):
		for operation in OPERATIONS:
			with self.subTest(operation=operation):
				control = StopControl()
				control.begin.set()
				events = []
				parameters = {"exponent": 127} if OPERATIONS[operation].requires_exponent else {}
				options = {"operation": operation}
				if parameters:
					options["parameters"] = parameters
				with patch("gui_monitor._cli_once", return_value=(0, False)) as once:
					self.assertEqual(run_operation("unused", "prime.ini", operation, control, events.append, parameters=parameters), 0)
					once.assert_called_once_with("unused", "prime.ini", control, **options)
				self.assertEqual([event["event"] for event in events], ["ready", "cycle_started", "operation_finished", "stopped"])
				self.assertEqual(events[-2]["server_confirmation"], "unverified")

	def test_startup_stop_cancels_one_shot_before_begin(self):
		control = StopControl()
		events = []
		def emit(message):
			events.append(message)
			if message["event"] == "ready":
				control.stop.set()
		with patch("gui_monitor._cli_once") as once:
			self.assertEqual(run_operation("unused", "prime.ini", "ping", control, emit), 0)
			once.assert_not_called()
		self.assertEqual([event["event"] for event in events], ["ready", "stopped"])

	def test_failure_and_force_do_not_claim_completion(self):
		for outcome in ((1, False), (-15, True)):
			with self.subTest(outcome=outcome):
				control = StopControl()
				control.begin.set()
				events = []
				with patch("gui_monitor._cli_once", return_value=outcome):
					code = run_operation("unused", "prime.ini", "upload_proofs", control, events.append)
				self.assertNotIn("operation_finished", [event["event"] for event in events])
				self.assertEqual(code, 0 if outcome[1] else 1)

	def test_cli_flags_are_allowlisted_noninteractive_and_do_not_include_secrets(self):
		for key, operation in OPERATIONS.items():
			with self.subTest(operation=key), patch("gui_monitor.subprocess.Popen") as popen:
				popen.return_value.wait.return_value = 0
				parameters = {"exponent": 127} if operation.requires_exponent else {}
				self.assertEqual(_cli_once("fixture workspace", "private.ini", StopControl(), operation=key, parameters=parameters), (0, False))
				arguments = popen.call_args.args[0]
				self.assertEqual(arguments[3:], ["--workdir", "fixture workspace", "--config-file", "private.ini", "--timeout", "0", *operation_arguments(key, parameters)])
				self.assertEqual(popen.call_args.kwargs["stdin"], subprocess.DEVNULL)
				self.assertEqual(popen.call_args.kwargs["stdout"], subprocess.DEVNULL)
				self.assertNotIn("shell", popen.call_args.kwargs)

	def test_unknown_operations_are_rejected_before_launch(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			with patch("gui_controller.subprocess.Popen") as popen:
				with self.assertRaises(ControllerError):
					MonitorController().start(document, operation="--recover-all")
				popen.assert_not_called()
			with patch("gui_monitor._cli_once") as once:
				with self.assertRaises(WorkspaceError):
					run_operation(directory, "prime.ini", "unknown", StopControl(), lambda _: None)
				once.assert_not_called()

	def test_real_supervisor_one_shot_releases_lock_and_preserves_config(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			controller = MonitorController(process_factory=fake_monitor_process)
			controller.start(document, operation="report_results")
			wait_event(controller, "cycle_started")
			with self.assertRaises(WorkspaceError):
				save_configuration(document, document.values(), "mlucas", [{"directory": "", "preference": ""}])
			finished = wait_event(controller, "operation_finished")
			self.assertEqual(finished["operation"], "report_results")
			wait_event(controller, "exited")
			self.assertFalse(controller.active)
			base = Path(directory)
			self.assertEqual((base / "operation.record").read_text(), "report_results")
			self.assertEqual((base / "cycles.record").read_text(), "simulated\n")
			self.assertEqual(document.path.read_bytes(), document.data)
			self.assertEqual(len(list(base.glob("*.gui-monitor-backup-*.bak"))), 1)

	def test_test_email_preflight_requires_saved_enabled_settings(self):
		for extra in ("", "[Email]\nfrom_email=sender@example.org\nsmtp_server=localhost\nsend=False\n"):
			with self.subTest(extra=extra), tempfile.TemporaryDirectory() as directory:
				document = fixture(directory)
				document.path.write_text(document.text + extra)
				document = ConfigDocument(directory)
				controller = MonitorController(process_factory=fake_monitor_process)
				controller.start(document, operation="test_email")
				wait_event(controller, "failed")
				wait_event(controller, "exited")
				self.assertFalse((Path(directory) / "operation.record").exists())
				self.assertFalse(list(Path(directory).glob("*.bak")))


if __name__ == "__main__":
	unittest.main()
