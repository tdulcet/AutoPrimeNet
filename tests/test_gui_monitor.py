"""Monitoring lifecycle tests. No test invokes a live PrimeNet cycle.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import time
import os
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument, WorkspaceError, instance_lease, save_configuration
from gui_controller import ControllerError, MonitorController
from gui_monitor import StopControl, _cli_once, cli_cycle, run_schedule


def fake_monitor_process(_command, **kwargs):
	"""Use the real supervisor/preflight/control protocol with a fake CLI cycle."""
	code = textwrap.dedent('''
		import gui_monitor, sys, time
		from pathlib import Path
		def fake_cycle(directory, config_name, control):
			with (Path(directory) / 'cycles.record').open('a') as stream:
				stream.write('simulated\\n')
			time.sleep(0.15)
			(Path(directory) / 'cycle.completed').write_text('completed')
			return 0, False
		gui_monitor.cli_cycle = fake_cycle
		def fake_once(directory, config_name, control, operation=None):
			(Path(directory) / 'operation.record').write_text(str(operation))
			return fake_cycle(directory, config_name, control)
		gui_monitor._cli_once = fake_once
		sys.exit(gui_monitor.main())
	''')
	return subprocess.Popen([sys.executable, "-B", "-c", code], **kwargs)


def fixture(directory):
	path = Path(directory) / "prime.ini"
	path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
	return ConfigDocument(directory)


def wait_event(controller, wanted, timeout=10):
	deadline = time.monotonic() + timeout
	while time.monotonic() < deadline:
		message = controller.events.get(timeout=max(deadline - time.monotonic(), 0.01))
		if message["event"] == wanted:
			return message
	raise AssertionError("Missing monitor event: " + wanted)


class ScheduleTests(unittest.TestCase):
	def test_stop_during_preflight_prevents_first_cycle(self):
		control = StopControl()
		events = []
		def emit(message):
			events.append(message)
			if message["event"] == "ready":
				control.stop.set()
		with patch("gui_monitor.cli_cycle") as cycle:
			self.assertEqual(run_schedule("unused", "prime.ini", 3600, control, emit), 0)
			cycle.assert_not_called()
		self.assertEqual([event["event"] for event in events], ["ready", "stopped"])

	def test_stop_after_cycle_does_not_claim_server_success_or_start_again(self):
		control = StopControl()
		control.begin.set()
		events = []
		def cycle(*_args):
			control.stop.set()
			return 0, False
		self.assertEqual(run_schedule("unused", "prime.ini", 3600, control, events.append, cycle), 0)
		self.assertEqual([event["event"] for event in events], ["ready", "cycle_started", "cycle_finished", "stopped"])
		self.assertEqual(events[2]["server_confirmation"], "unverified")

	def test_cycle_failure_does_not_retry_indefinitely(self):
		control = StopControl()
		control.begin.set()
		events = []
		self.assertEqual(run_schedule("unused", "prime.ini", 3600, control, events.append, lambda *_: (7, False)), 1)
		self.assertEqual(events[-1], {"event": "failed", "exit_code": 7})
		self.assertNotIn("cycle_finished", [event["event"] for event in events])

	def test_initial_registration_followup_and_stop_between_passes(self):
		for stopping in (False, True):
			with self.subTest(stopping=stopping), tempfile.TemporaryDirectory() as directory:
				document = fixture(directory)
				control = StopControl()
				def first_pass(*_args):
					document.path.write_text(document.text + "ComputerGUID=0123456789abcdef0123456789abcdef\n")
					if stopping:
						control.stop.set()
					return 0, False
				with patch("gui_monitor._cli_once", side_effect=first_pass) as cycle:
					self.assertEqual(cli_cycle(directory, "prime.ini", control), (0, False))
					self.assertEqual(cycle.call_count, 1 if stopping else 2)

	def test_cli_argv_contains_no_credentials_and_uses_noninteractive_one_pass(self):
		with patch("gui_monitor.subprocess.Popen") as popen:
			popen.return_value.wait.return_value = 0
			self.assertEqual(_cli_once("/fixture", "prime.ini", StopControl()), (0, False))
			command = popen.call_args.args[0]
			self.assertEqual(command[-2:], ["--timeout", "0"])
			self.assertNotIn("--password", command)
			self.assertEqual(popen.call_args.kwargs["stdin"], subprocess.DEVNULL)
			self.assertNotIn("shell", popen.call_args.kwargs)

	def test_force_stop_terminates_only_the_owned_test_child(self):
		control = StopControl()
		process = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])
		unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])
		try:
			control.force.set()
			with patch("gui_monitor.subprocess.Popen", return_value=process):
				_code, forced = _cli_once("/fixture", "prime.ini", control)
			self.assertTrue(forced)
			self.assertIsNotNone(process.poll())
			self.assertIsNone(unrelated.poll())
		finally:
			if process.poll() is None:
				process.kill()
			process.wait()
			unrelated.terminate()
			unrelated.wait()


class MonitorProcessTests(unittest.TestCase):
	def make_controller(self):
		controller = MonitorController(process_factory=fake_monitor_process)
		self.addCleanup(self.stop_controller, controller)
		return controller

	def stop_controller(self, controller):
		controller.stop(force=True)
		if controller.process is not None:
			controller.process.wait(timeout=8)

	def test_real_supervisor_preflight_wait_stop_and_save_lock(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			controller = self.make_controller()
			controller.start(document)
			wait_event(controller, "cycle_finished")
			self.assertTrue(controller.active)
			with self.assertRaises(ControllerError):
				controller.start(document)
			with self.assertRaises(WorkspaceError):
				save_configuration(document, document.values(), "mlucas", [{"directory": "", "preference": ""}])
			controller.stop()
			wait_event(controller, "exited")
			self.assertEqual(controller.process.returncode, 0)
			self.assertEqual((Path(directory) / "cycles.record").read_text(), "simulated\n")
			backups = list(Path(directory).glob("prime.ini.gui-monitor-backup-*.bak"))
			self.assertEqual(len(backups), 1)
			self.assertEqual(backups[0].read_bytes(), document.data)
			if os.name != "nt":
				self.assertEqual(backups[0].stat().st_mode & 0o777, 0o600)
			with instance_lease(directory, "~gui-monitor.lock"):
				pass

	def test_duplicate_gui_supervisor_refused_without_affecting_first(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			first = self.make_controller()
			second = self.make_controller()
			first.start(document)
			wait_event(first, "cycle_finished")
			second.start(document)
			wait_event(second, "failed")
			wait_event(second, "exited")
			self.assertTrue(first.active)
			first.stop()
			wait_event(first, "exited")

	def test_independent_cli_lock_and_stale_configuration_refused(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			controller = self.make_controller()
			with instance_lease(directory):
				controller.start(document)
				wait_event(controller, "failed")
				wait_event(controller, "exited")
			document.path.write_text(document.text + "ComputerID=external\n")
			controller.start(document)
			wait_event(controller, "failed")
			wait_event(controller, "exited")
			self.assertFalse((Path(directory) / "cycles.record").exists())

	def test_parent_pipe_eof_requests_graceful_shutdown(self):
		with tempfile.TemporaryDirectory() as directory:
			controller = self.make_controller()
			controller.start(fixture(directory))
			wait_event(controller, "cycle_finished")
			with controller._control_lock:
				controller.process.stdin.close()
			wait_event(controller, "exited")
			self.assertEqual(controller.process.returncode, 0)

	def test_stop_during_running_cycle_waits_for_completion(self):
		with tempfile.TemporaryDirectory() as directory:
			controller = self.make_controller()
			controller.start(fixture(directory))
			wait_event(controller, "cycle_started")
			controller.stop()
			wait_event(controller, "exited")
			self.assertEqual((Path(directory) / "cycle.completed").read_text(), "completed")
			self.assertEqual(controller.process.returncode, 0)

	def test_stop_while_preflight_is_still_running_does_not_begin_cycle(self):
		with tempfile.TemporaryDirectory() as directory:
			controller = self.make_controller()
			controller.start(fixture(directory))
			controller.stop()
			wait_event(controller, "exited")
			self.assertFalse((Path(directory) / "cycles.record").exists())


if __name__ == "__main__":
	unittest.main()
