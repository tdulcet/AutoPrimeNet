"""Tests for responsive job delivery and offline process calls.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import threading
import time
import unittest
from unittest import mock
from types import SimpleNamespace
import json
import io
import subprocess

from gui_controller import BackgroundJobs, ControllerError, MonitorController, TrayController, backend_request, monitor_message


class ControllerTests(unittest.TestCase):
	def test_monitor_event_fields_cannot_break_tk_polling(self):
		for message in (
			{"event": "ready"}, {"event": "ready", "interval": True},
			{"event": "ready", "operation": []}, {"event": "ready", "operation": "unknown"},
			{"event": "ready", "interval": -1}, {"event": "failed", "error": {}},
			{"event": "failed", "error": None}, {"event": "ready", "interval": 0, "assignment_backup": []},
			{"event": "trace_created", "name": "../private"}, {"event": "trace_created", "name": ""},
			*({"event": "cycle_finished", "time": value, "next_cycle": 1} for value in (None, True, "x", float("nan"), float("inf"), 10 ** 100)),
		):
			with self.subTest(message=message):
				self.assertFalse(monitor_message(message))
		for message in ({"event": "ready", "interval": 0}, {"event": "ready", "operation": "status"}, {"event": "failed", "error": "fixture"},
			{"event": "cycle_finished", "time": 0, "next_cycle": 1.5},
			{"event": "trace_created", "name": ".gui-backend-trace-fixture.log"}):
			self.assertTrue(monitor_message(message))
	def test_repeated_click_is_rejected_until_result_consumed(self):
		jobs = BackgroundJobs()
		release = threading.Event()
		try:
			self.assertTrue(jobs.submit("first", release.wait, 2))
			self.assertFalse(jobs.submit("duplicate", lambda: None))
			release.set()
			deadline = time.monotonic() + 3
			result = None
			while result is None and time.monotonic() < deadline:
				result = jobs.take()
				if result is None:
					time.sleep(0.01)
			self.assertEqual(result, ("first", True, None))
			self.assertFalse(jobs.busy)
		finally:
			release.set()
			jobs.close()
		self.assertFalse(jobs.submit("closed", lambda: None))

	def test_backend_failure_is_not_reported_as_success(self):
		with self.assertRaisesRegex(ControllerError, "Unsupported offline bridge operation"):
			backend_request("unreserve_all")

	def test_oversized_request_rejected_before_launch(self):
		with self.assertRaisesRegex(ControllerError, "1 MiB"):
			backend_request("parse_work", lines=["x" * (1024 * 1024)])
	def test_malformed_backend_envelopes_are_controlled_errors(self):
		for response in (None, [], "unexpected", {},
			{"protocol": 1, "ok": True},
			{"protocol": 1, "ok": 1, "result": {}},
			{"protocol": 1, "ok": False, "error": {"private": "data"}}):
			with self.subTest(response=response), mock.patch(
				"gui_controller.subprocess.run",
				return_value=SimpleNamespace(stdout=json.dumps(response), returncode=0),
			):
				with self.assertRaisesRegex(ControllerError, "Unexpected offline backend response"):
					backend_request("capabilities")

	def test_invalid_event_types_do_not_end_helper_readers(self):
		lines = '\n'.join(json.dumps(value) for value in (
			None, [], {"event": []}, {"event": {}}, {"event": "unknown"},
			{"event": "stopped"}, {"event": "open"},
		)) + '\n'
		for controller, wanted, final in (
			(MonitorController(), "stopped", "exited"),
			(TrayController(), "open", "unavailable"),
		):
			with self.subTest(controller=type(controller).__name__):
				process = mock.Mock(stdout=io.StringIO(lines), stdin=io.StringIO())
				process.wait.return_value = 0
				controller._read(process, 7)
				self.assertEqual(controller.events.get_nowait()["event"], wanted)
				self.assertEqual(controller.events.get_nowait()["event"], final)

	def test_startup_pipe_failure_returns_before_cleanup_finishes(self):
		release = threading.Event()
		waiting = threading.Event()
		def wait(**kwargs):
			waiting.set()
			release.wait(3)
			return 0
		process = mock.Mock()
		process.poll.return_value = None
		process.stdin.flush.side_effect = BrokenPipeError("fixture")
		process.stdin.close.side_effect = BrokenPipeError("fixture close")
		process.wait.side_effect = wait
		controller = MonitorController(process_factory=mock.Mock(return_value=process))
		document = SimpleNamespace(version=1, directory="fixture", path=SimpleNamespace(name="prime.ini"), data=b"fixture")
		try:
			with self.assertRaisesRegex(ControllerError, "Could not launch"):
				controller.start(document)
			self.assertTrue(waiting.wait(1))
			self.assertTrue(controller.active)
			with self.assertRaisesRegex(ControllerError, "already active"):
				controller.start(document)
			self.assertTrue(controller.events.empty())
		finally:
			release.set()
		self.assertEqual(controller.events.get(timeout=3)["event"], "exited")
		process.terminate.assert_called_once()
		process.stdout.close.assert_called_once()

	def test_failed_start_cleanup_escalates_and_reaps_owned_process(self):
		controller = MonitorController()
		old = mock.Mock()
		old.poll.return_value = None
		old.terminate.side_effect = ProcessLookupError()
		old.wait.side_effect = [subprocess.TimeoutExpired("fixture", 2), 9]
		replacement = mock.Mock()
		controller.process = replacement
		controller._abort_start(old, 3)
		old.kill.assert_called_once()
		self.assertEqual(old.wait.call_count, 2)
		replacement.terminate.assert_not_called()
		replacement.kill.assert_not_called()
		self.assertEqual(controller.events.get_nowait(), {"event": "exited", "exit_code": 9, "generation": 3})


if __name__ == "__main__":
	unittest.main()
