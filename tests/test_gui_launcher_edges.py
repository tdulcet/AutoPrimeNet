"""Failure, concurrency and lifecycle boundaries for computation launchers."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import psutil

from gui_computation import ROOT, computation_guard, duplicate_processes, launch_computation, plan_digest, prepare_launch, resolve_profile, run_computation, select_terminal, session_status
from gui_computation import FILENAME, MAX_BYTES, LaunchError, defaults, file_lock, load_settings, read_bytes, save_settings, validate_settings, write_json


def profile(**changes):
	return {"name": "Worker", "program": "Mlucas", "executable": sys.executable, "directory": "", "arguments": [], "terminal": "auto", **changes}


class StorageEdges(unittest.TestCase):
	def test_schema_limits_and_all_supported_program_profiles(self):
		from gui_computation import PROGRAMS
		for program in PROGRAMS:
			self.assertEqual(validate_settings({**defaults(), "profiles": [profile(program=program)]})["profiles"][0]["program"], program)
		valid = {**defaults(), "profiles": [profile(name="x" * 80, arguments=["x" * 4096])], "refresh_seconds": 86400}
		validate_settings(valid)
		validate_settings({**defaults(), "profiles": [profile(name=str(i)) for i in range(128)]})
		validate_settings({**defaults(), "profiles": [profile(arguments=[""] * 128)], "refresh_seconds": 1})
		invalid = [None, [], {**defaults(), "version": True}, {**defaults(), "version": 2}, {**defaults(), "unknown": 1},
			{**defaults(), "profiles": [profile(name="a"), profile(name="A")]},
			{**defaults(), "profiles": [profile(name="x" * 81)]},
			{**defaults(), "profiles": [profile(arguments=["a"] * 129)]},
			{**defaults(), "profiles": [profile(arguments=["x" * 4097])]},
			{**defaults(), "profiles": [profile(arguments=["a\x00b"])]},
			{**defaults(), "profiles": [profile(program="unknown")]},
			{**defaults(), "profiles": [profile(extra=True)]},
			{**defaults(), "profiles": [profile(name=str(i)) for i in range(129)]}]
		for value in invalid:
			with self.subTest(value=repr(value)[:100]), self.assertRaises(LaunchError):
				validate_settings(value)

	def test_serialized_size_limit_and_failed_replace_preserve_original(self):
		with tempfile.TemporaryDirectory() as temp:
			settings, version = save_settings(temp, defaults(), None)
			path = Path(temp, FILENAME)
			before = path.read_bytes()
			with self.assertRaises(LaunchError):
				save_settings(temp, {**defaults(), "profiles": [profile(arguments=["λ" * 4096] * 10)]}, version)
			self.assertEqual(path.read_bytes(), before)
			with self.assertRaises(LaunchError):
				write_json(path, {"too_large": "x" * MAX_BYTES})
			self.assertEqual(path.read_bytes(), before)
			with patch("gui_computation.os.replace", side_effect=OSError("fixture disk error")):
				with self.assertRaises(OSError):
					save_settings(temp, {**settings, "refresh_seconds": 10}, version)
			self.assertEqual(path.read_bytes(), before)
			self.assertEqual(list(Path(temp).glob(".launcher-*")), [])
			path.write_bytes(b"x" * (MAX_BYTES + 1))
			with self.assertRaises(LaunchError):
				load_settings(temp)

	def test_replaced_file_and_nonregular_inputs_are_refused_without_blocking(self):
		with tempfile.TemporaryDirectory() as temp:
			first, second = Path(temp, "first"), Path(temp, "second")
			first.write_text("first")
			second.write_text("second")
			original_open = os.open
			def replacement(path, flags, *args):
				return original_open(second if Path(path) == first else path, flags, *args)
			with patch("gui_computation.os.open", side_effect=replacement):
				with self.assertRaises(LaunchError):
					read_bytes(first)
			if hasattr(os, "mkfifo"):
				fifo = Path(temp, "fifo")
				os.mkfifo(fifo)
				with self.assertRaises(LaunchError):
					read_bytes(fifo)
				with self.assertRaises(LaunchError):
					with file_lock(fifo):
						self.fail("Locked a nonregular file")

	def test_interprocess_profile_lock_refuses_writes_and_releases(self):
		with tempfile.TemporaryDirectory() as temp:
			lock, ready = Path(temp, ".autoprimenet-gui-launchers.lock"), Path(temp, "ready")
			code = "from gui_computation import file_lock; from pathlib import Path; import sys\nwith file_lock(sys.argv[1]):\n Path(sys.argv[2]).touch()\n sys.stdin.read()"
			child = subprocess.Popen([sys.executable, "-B", "-c", code, str(lock), str(ready)], cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
			try:
				deadline = time.monotonic() + 10
				while not ready.exists() and child.poll() is None and time.monotonic() < deadline:
					time.sleep(.02)
				self.assertTrue(ready.exists())
				with self.assertRaises(LaunchError):
					save_settings(temp, defaults(), None)
				self.assertFalse(Path(temp, FILENAME).exists())
			finally:
				child.communicate(timeout=5)
			save_settings(temp, defaults(), None)

	def test_symlink_lock_and_session_directory_are_not_followed(self):
		if not hasattr(os, "symlink"):
			self.skipTest("Symlinks unavailable")
		with tempfile.TemporaryDirectory() as temp:
			base = Path(temp)
			target = base / "target"
			target.write_bytes(b"unchanged")
			try:
				(base / ".autoprimenet-gui-launchers.lock").symlink_to(target)
			except OSError:
				self.skipTest("Symlink creation not permitted")
			with self.assertRaises((OSError, LaunchError)):
				save_settings(temp, defaults(), None)
			self.assertEqual(target.read_bytes(), b"unchanged")
			outside = base / "outside"
			outside.mkdir()
			(base / ".autoprimenet-gui-launches").symlink_to(outside, target_is_directory=True)
			with patch("gui_computation.prepare_launch", return_value={"plan": {}, "terminal": "xterm", "terminal_executable": "xterm"}), patch("gui_computation.subprocess.Popen") as spawn:
				with self.assertRaises(LaunchError):
					launch_computation(temp, profile(), None, {"plan": {}, "terminal": "xterm", "terminal_executable": "xterm"})
				spawn.assert_not_called()
			self.assertEqual(list(outside.iterdir()), [])


class LaunchEdges(unittest.TestCase):
	def test_missing_executable_directory_and_nonexecutable_fail_before_terminal(self):
		with tempfile.TemporaryDirectory() as temp:
			with patch("gui_computation.shutil.which", return_value=None):
				with self.assertRaises(LaunchError):
					resolve_profile(temp, profile(executable="missing-engine"))
			with self.assertRaises(OSError):
				resolve_profile(temp, profile(directory="missing-directory"))
			with self.assertRaises(LaunchError):
				resolve_profile(temp, profile(executable=temp))
			if os.name != "nt":
				executable = Path(temp, "not-executable")
				executable.touch()
				with self.assertRaises(LaunchError):
					resolve_profile(temp, profile(executable=str(executable)))
			with patch("gui_computation.shutil.which", return_value=sys.executable):
				self.assertEqual(Path(resolve_profile(temp, profile(executable="engine"))["argv"][0]), Path(sys.executable).resolve())

	def test_terminal_auto_priority_and_wrong_platform_combinations(self):
		for executable, expected in (("pwsh.exe", "PowerShell"), ("powershell.exe", "PowerShell"), ("cmd.exe", "Cmd")):
			self.assertEqual(select_terminal("auto", "win32", lambda name, executable=executable: name if name == executable else None)[0], expected)
		for name in ("ptyxis", "gnome-terminal", "konsole", "xfce4-terminal", "xterm"):
			self.assertEqual(select_terminal("auto", "freebsd14", lambda value, name=name: value if value == name else None)[0], name)
		for preference, platform in (("PowerShell", "linux"), ("xterm", "win32"), ("auto", "darwin"), ("unknown", "linux")):
			with self.assertRaises(LaunchError):
				select_terminal(preference, platform, lambda _: None)

	def test_duplicate_processes_match_directory_and_handle_permissions_and_exits(self):
		with tempfile.TemporaryDirectory() as temp:
			plan = resolve_profile(temp, profile())
			def process(pid, name, executable, directory):
				return SimpleNamespace(pid=pid, name=Mock(return_value=name), exe=Mock(return_value=executable), cwd=Mock(return_value=directory))
			matching = process(1, "Mlucas", "/renamed/engine", temp)
			renamed = process(2, "custom", plan["argv"][0], temp)
			other = process(3, "Mlucas", plan["argv"][0], str(Path(temp).parent))
			denied = process(4, "Mlucas", plan["argv"][0], temp)
			denied.cwd.side_effect = psutil.AccessDenied(4)
			exited = process(5, "Mlucas", plan["argv"][0], temp)
			exited.name.side_effect = psutil.NoSuchProcess(5)
			fallback = process(6, "Mlucas", "", temp)
			fallback.exe.side_effect = psutil.AccessDenied(6)
			with patch("psutil.process_iter", return_value=iter([matching, renamed, other, denied, exited, fallback])):
				matches, inaccessible = duplicate_processes(plan)
			self.assertEqual(matches, [1, 2, 6])
			self.assertGreaterEqual(inaccessible, 1)

	def test_duplicate_check_excludes_the_helper_itself(self):
		with tempfile.TemporaryDirectory() as temp:
			plan = resolve_profile(temp, profile())
			process = SimpleNamespace(pid=os.getpid(), name=lambda: "Mlucas", exe=lambda: plan["argv"][0], cwd=lambda: temp)
			with patch("psutil.process_iter", return_value=iter([process])):
				self.assertEqual(duplicate_processes(plan), ([], 0))

	def test_unreadable_executable_identity_reports_incomplete_duplicate_detection(self):
		with tempfile.TemporaryDirectory() as temp:
			plan = resolve_profile(temp, profile())
			process = SimpleNamespace(pid=123, name=lambda: "custom-worker", exe=Mock(side_effect=psutil.AccessDenied(123)), cwd=lambda: temp)
			with patch("psutil.process_iter", return_value=iter([process])):
				self.assertEqual(duplicate_processes(plan), ([], 1))

	def test_windows_terminal_launch_keeps_console_streams_and_static_cmd_script(self):
		for terminal in ("PowerShell", "Cmd"):
			with self.subTest(terminal=terminal), tempfile.TemporaryDirectory() as temp:
				with patch("gui_computation.sys.platform", "win32"), patch("gui_computation.select_terminal", return_value=(terminal, "terminal.exe")), patch("gui_computation.duplicate_processes", return_value=([], 0)), patch("gui_computation.subprocess.Popen") as spawn:
					spawn.return_value.wait.return_value = 0
					item = profile(arguments=["%PATH%! & λ"])
					result = launch_computation(temp, item, None, prepare_launch(temp, item, None))
					options = spawn.call_args.kwargs
					for key in ("stdin", "stdout", "stderr", "start_new_session"):
						self.assertNotIn(key, options)
					self.assertEqual(options["creationflags"], 0x10)
					if terminal == "Cmd":
						script = Path(result["session"], "launch.cmd").read_text()
						self.assertIn("DisableDelayedExpansion", script)
						self.assertNotIn("%PATH%! & λ", script)
						self.assertEqual(options["env"]["APN_GUI_PAYLOAD"], str(Path(result["session"], "launch.json")))

	def test_terminal_nonzero_exit_does_not_overwrite_engine_acknowledgement(self):
		for running in (False, True):
			with self.subTest(running=running), tempfile.TemporaryDirectory() as temp:
				def wait(running=running):
					if running:
						path = next(Path(temp).glob(".autoprimenet-gui-launches/*/status.json"))
						write_json(path, {"state": "running", "pid": 123})
					return 1
				with patch("gui_computation.select_terminal", return_value=("xterm", "xterm")), patch("gui_computation.duplicate_processes", return_value=([], 0)), patch("gui_computation.subprocess.Popen") as spawn:
					spawn.return_value.wait.side_effect = wait
					result = launch_computation(temp, profile(), None, prepare_launch(temp, profile(), None))
					deadline = time.monotonic() + 3
					while session_status(result["session"])["state"] == "waiting" and time.monotonic() < deadline:
						time.sleep(.01)
					self.assertEqual(session_status(result["session"])["state"], "running" if running else "failed")

	def test_helper_cli_rejects_bad_invocations_and_reports_malformed_payload(self):
		helper = ROOT / "gui_computation.py"
		bad = subprocess.run([sys.executable, "-B", str(helper), "--unexpected"], capture_output=True, text=True, timeout=10)
		self.assertNotEqual(bad.returncode, 0)
		with tempfile.TemporaryDirectory() as temp:
			payload = Path(temp, "launch.json")
			write_json(payload, {})
			result = subprocess.run([sys.executable, "-B", str(helper), "--run", plan_digest({}), str(payload)], input="\n", capture_output=True, text=True, timeout=10)
			self.assertEqual(result.returncode, 1)
			self.assertIn("Unable to start computation", result.stderr)
			self.assertEqual(session_status(temp)["state"], "failed")

	def test_terminal_rejects_valid_but_substituted_payload(self):
		with tempfile.TemporaryDirectory() as temp:
			payload = Path(temp, "launch.json")
			plan = resolve_profile(temp, profile())
			expected = plan_digest(plan)
			write_json(payload, {**plan, "argv": [*plan["argv"], "--other"]})
			with patch("gui_computation.subprocess.Popen") as spawn:
				self.assertEqual(run_computation(payload, pause=False, expected_digest=expected), 1)
				spawn.assert_not_called()

	def test_helper_records_nonzero_exit_and_waits_for_terminal_acknowledgement(self):
		with tempfile.TemporaryDirectory() as temp:
			session = Path(temp, "sessions", "one")
			session.mkdir(parents=True)
			payload = session / "launch.json"
			write_json(payload, resolve_profile(temp, profile(arguments=["-c", "raise SystemExit(7)"])))
			with patch("gui_computation.duplicate_processes", return_value=([], 0)), patch("builtins.input", side_effect=EOFError) as pause:
				self.assertEqual(run_computation(payload), 7)
				pause.assert_called_once()
			self.assertEqual(session_status(session)["exit_code"], 7)

	def test_status_write_failure_still_waits_for_engine_and_holds_launch_lock(self):
		with tempfile.TemporaryDirectory() as temp:
			session = Path(temp, "sessions", "one")
			session.mkdir(parents=True)
			payload = session / "launch.json"
			plan = resolve_profile(temp, profile())
			write_json(payload, plan)
			def wait():
				with self.assertRaises(LaunchError):
					with computation_guard(payload, plan):
						self.fail("Released computation guard before engine exit")
				return 0
			with patch("gui_computation.duplicate_processes", return_value=([], 0)), patch("gui_computation.subprocess.Popen") as spawn, patch("gui_computation.write_json", side_effect=OSError("fixture disk full")):
				spawn.return_value.pid = 123
				spawn.return_value.wait.side_effect = wait
				self.assertEqual(run_computation(payload, pause=False), 0)
				spawn.return_value.wait.assert_called_once()

	def test_malformed_payload_and_missing_engine_fail_without_spawning(self):
		with tempfile.TemporaryDirectory() as temp:
			session = Path(temp, "sessions", "one")
			session.mkdir(parents=True)
			payload = session / "launch.json"
			for value in ([], {}, {"name": "fixture", "program": "Mlucas", "directory": temp, "argv": [str(Path(temp, "missing"))], "terminal": "auto"}):
				write_json(payload, value)
				with patch("gui_computation.subprocess.Popen") as spawn:
					self.assertEqual(run_computation(payload, pause=False), 1)
					spawn.assert_not_called()
				self.assertEqual(session_status(session)["state"], "failed")
