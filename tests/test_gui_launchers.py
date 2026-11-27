"""Launch-profile persistence, terminal argument boundaries and independent helpers."""

import base64
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from gui_computation import ROOT, computation_guard, console_python, launch_computation, prepare_launch, resolve_profile, run_computation, select_terminal, session_status, terminal_command
from gui_computation import FILENAME, LaunchError, defaults, load_settings, save_settings, write_json


def profile():
	return {"name": "CPU worker", "program": "Mlucas", "executable": sys.executable,
		"directory": "", "arguments": [], "terminal": "auto"}


class ProfileTests(unittest.TestCase):
	def test_missing_settings_do_not_create_files_and_default_to_90_seconds(self):
		with tempfile.TemporaryDirectory() as temp:
			settings, version = load_settings(temp)
			self.assertEqual(settings["refresh_seconds"], 90)
			self.assertIsNone(version)
			self.assertEqual(list(Path(temp).iterdir()), [])

	def test_profiles_and_interval_persist_per_workspace_and_preserve_engine_files(self):
		with tempfile.TemporaryDirectory() as temp, tempfile.TemporaryDirectory() as other:
			engine = Path(temp, "prime.ini")
			engine.write_bytes(b"untouched engine configuration\r\n")
			settings = {**defaults(), "profiles": [profile()], "refresh_seconds": 42}
			stored, version = save_settings(temp, settings, None)
			self.assertEqual(stored, settings)
			self.assertEqual(load_settings(temp), (stored, version))
			self.assertEqual(load_settings(other), (defaults(), None))
			self.assertEqual(engine.read_bytes(), b"untouched engine configuration\r\n")
			if os.name != "nt":
				self.assertEqual(Path(temp, FILENAME).stat().st_mode & 0o777, 0o600)

	def test_external_edit_is_not_overwritten(self):
		with tempfile.TemporaryDirectory() as temp:
			settings, version = save_settings(temp, defaults(), None)
			Path(temp, FILENAME).write_text(json.dumps({**settings, "refresh_seconds": 50}))
			with self.assertRaisesRegex(LaunchError, "changed externally"):
				save_settings(temp, settings, version)

	def test_invalid_settings_and_symlinks_are_refused(self):
		for value in (0, -1, True, 86401, "90"):
			with tempfile.TemporaryDirectory() as temp, self.subTest(value=value):
				with self.assertRaises(LaunchError):
					save_settings(temp, {**defaults(), "refresh_seconds": value}, None)
		with tempfile.TemporaryDirectory() as temp:
			Path(temp, FILENAME).write_text("not JSON")
			with self.assertRaises(LaunchError):
				save_settings(temp, defaults(), None)
			self.assertEqual(Path(temp, FILENAME).read_text(), "not JSON")
			if os.name != "nt":
				Path(temp, FILENAME).unlink()
				target = Path(temp, "target")
				target.write_text(json.dumps(defaults()))
				Path(temp, FILENAME).symlink_to(target)
				with self.assertRaises(LaunchError):
					load_settings(temp)

	def test_duplicate_names_invalid_arguments_and_unknown_schema(self):
		for profiles in ([profile(), profile()], [{**profile(), "arguments": "-h"}], [{**profile(), "arguments": ["a\nb"]}], [{**profile(), "terminal": "unknown"}]):
			with tempfile.TemporaryDirectory() as temp:
				with self.assertRaises(LaunchError):
					save_settings(temp, {**defaults(), "profiles": profiles}, None)

	def test_relative_executable_and_worker_directory_resolution(self):
		with tempfile.TemporaryDirectory() as temp:
			base = Path(temp)
			(base / "worker 1").mkdir()
			executable = base / "Mlucas"
			executable.write_text("fixture")
			executable.chmod(0o700)
			if os.name == "nt":
				executable = executable.rename(base / "Mlucas.exe")
			plan = resolve_profile(temp, {**profile(), "executable": "./" + executable.name, "directory": "worker 1"})
			self.assertEqual(Path(plan["directory"]), (base / "worker 1").resolve())
			self.assertEqual(Path(plan["argv"][0]), executable.resolve())


class TerminalTests(unittest.TestCase):
	def test_windowed_python_uses_console_interpreter(self):
		with tempfile.TemporaryDirectory() as temp:
			windowed, console = Path(temp, "pythonw.exe"), Path(temp, "python.exe")
			console.touch()
			with patch("gui_computation.sys.platform", "win32"), patch("gui_computation.sys.executable", str(windowed)):
				self.assertEqual(console_python(), str(console))
				console.unlink()
				with self.assertRaises(LaunchError):
					console_python()

	def test_terminal_selection_and_missing_terminal_failures(self):
		which = lambda name: "/usr/bin/" + name if name in {"xterm", "osascript", "powershell.exe"} else None
		self.assertEqual(select_terminal("auto", "linux", which)[0], "xterm")
		self.assertEqual(select_terminal("auto", "darwin", which)[0], "Terminal")
		self.assertEqual(select_terminal("auto", "win32", which)[0], "PowerShell")
		with self.assertRaises(LaunchError):
			select_terminal("konsole", "linux", which)
		with self.assertRaises(LaunchError):
			select_terminal("Cmd", "darwin", which)

	def test_linux_terminals_use_argument_arrays_without_shell_interpolation(self):
		payload = Path("/tmp/work space/'literal;$()/launch.json")
		for name in ("ptyxis", "gnome-terminal", "konsole", "xfce4-terminal", "xterm"):
			argv, options = terminal_command(name, "/bin/" + name, payload, "0" * 64, python="/python with spaces", platform="linux")
			self.assertEqual(argv[-1], str(payload))
			self.assertIn("/python with spaces", argv)
			self.assertTrue(options["start_new_session"])
			self.assertNotIn("shell", options)

	def test_powershell_payload_only_contains_quoted_helper_paths(self):
		payload = Path("/tmp/quote's $() & space/launch.json")
		argv, options = terminal_command("PowerShell", "powershell.exe", payload, "0" * 64, python="C:/Python's/python.exe", platform="win32")
		command = base64.b64decode(argv[-1]).decode("utf-16-le")
		self.assertIn("'C:/Python''s/python.exe'", command)
		self.assertIn("quote''s $() & space", command)
		self.assertIn("-NoExit", argv)
		self.assertEqual(options["creationflags"], 0x10)

	def test_cmd_uses_static_script_and_environment_for_dynamic_paths(self):
		payload = Path("/tmp/%PATH%! & work/launch.json")
		argv, options = terminal_command("Cmd", "cmd.exe", payload, "0" * 64, python="C:/Python & literal/python.exe", platform="win32")
		self.assertEqual(argv, ["cmd.exe", "/D", "/V:OFF", "/K", "launch.cmd"])
		self.assertEqual(options["env"]["APN_GUI_PAYLOAD"], str(payload))
		self.assertEqual(options["env"]["APN_GUI_PYTHON"], "C:/Python & literal/python.exe")

	def test_macos_quotes_helper_command_and_uses_fixed_applescript(self):
		import shlex
		payload = Path("/tmp/quote's & work/launch.json")
		argv, options = terminal_command("Terminal", "/usr/bin/osascript", payload, "0" * 64, python="/Python 'two'/python", platform="darwin")
		self.assertEqual(shlex.split(argv[-1])[-1], str(payload))
		self.assertEqual(shlex.split(argv[-1])[0], "/Python 'two'/python")
		self.assertNotIn(str(payload), argv[2])
		self.assertTrue(options["start_new_session"])

	def test_duplicates_and_changed_profiles_refuse_before_terminal_launch(self):
		with tempfile.TemporaryDirectory() as temp:
			with patch("gui_computation.select_terminal", return_value=("xterm", "/bin/xterm")), patch("gui_computation.duplicate_processes", return_value=([12], 0)):
				with self.assertRaisesRegex(LaunchError, "already running"):
					prepare_launch(temp, profile(), None)
			with self.assertRaisesRegex(LaunchError, "changed"):
				prepare_launch(temp, profile(), "old")

	def test_changed_engine_requires_another_review(self):
		with tempfile.TemporaryDirectory() as temp:
			engine = Path(temp, "engine.exe")
			engine.write_bytes(b"first")
			engine.chmod(0o700)
			item = {**profile(), "executable": str(engine)}
			with patch("gui_computation.select_terminal", return_value=("xterm", "xterm")), patch("gui_computation.duplicate_processes", return_value=([], 0)), patch("gui_computation.subprocess.Popen") as spawn:
				review = prepare_launch(temp, item, None)
				engine.write_bytes(b"replacement")
				with self.assertRaisesRegex(LaunchError, "changed after review"):
					launch_computation(temp, item, None, review)
				payload = Path(temp, "session", "one", "launch.json")
				payload.parent.mkdir(parents=True)
				write_json(payload, review["plan"])
				self.assertEqual(run_computation(payload, pause=False), 1)
				spawn.assert_not_called()

	def test_retargeted_symlink_never_starts_an_unreviewed_engine(self):
		with tempfile.TemporaryDirectory() as temp:
			base = Path(temp)
			for name in ("first.exe", "second.exe"):
				(base / name).touch(mode=0o700)
			link = base / "engine.exe"
			try:
				link.symlink_to(base / "first.exe")
			except OSError:
				self.skipTest("Symlink creation not permitted")
			item = {**profile(), "executable": str(link)}
			with patch("gui_computation.select_terminal", return_value=("xterm", "xterm")), patch("gui_computation.duplicate_processes", return_value=([], 0)), patch("gui_computation.subprocess.Popen") as spawn:
				review = prepare_launch(temp, item, None)
				link.unlink()
				link.symlink_to(base / "second.exe")
				with self.assertRaisesRegex(LaunchError, "changed after review"):
					launch_computation(temp, item, None, review)
				spawn.assert_not_called()

	def test_terminal_failure_and_session_creation_do_not_touch_engine_files(self):
		with tempfile.TemporaryDirectory() as temp:
			Path(temp, "worktodo.txt").write_text("untouched")
			with patch("gui_computation.select_terminal", return_value=("xterm", "/bin/missing")), patch("gui_computation.duplicate_processes", return_value=([], 0)), patch("gui_computation.subprocess.Popen", side_effect=OSError):
				with self.assertRaises(LaunchError):
					launch_computation(temp, profile(), None, prepare_launch(temp, profile(), None))
			self.assertEqual(Path(temp, "worktodo.txt").read_text(), "untouched")
			statuses = list(Path(temp).glob(".autoprimenet-gui-launches/*/status.json"))
			self.assertEqual(json.loads(statuses[0].read_text())["state"], "failed")


class HelperTests(unittest.TestCase):
	def make_payload(self, temp, arguments):
		base = Path(temp)
		session = base / "sessions" / "one"
		session.mkdir(parents=True)
		payload = session / "launch.json"
		plan = resolve_profile(base, {**profile(), "arguments": arguments})
		write_json(payload, plan)
		return payload, plan

	def test_native_helper_preserves_literal_arguments_and_records_exit(self):
		with tempfile.TemporaryDirectory() as temp:
			arguments = ['space argument', 'quote\'"', '$(touch injected)', '%PATH%! &', 'unicode λ']
			code = "import os,sys,json; open('observed.json','w').write(json.dumps([os.getcwd(),sys.argv[1:]]))"
			payload, _ = self.make_payload(temp, ["-c", code, *arguments])
			with patch("gui_computation.duplicate_processes", return_value=([], 0)):
				self.assertEqual(run_computation(payload, pause=False), 0)
			observed = json.loads(Path(temp, "observed.json").read_text())
			self.assertEqual(Path(observed[0]), Path(temp).resolve())
			self.assertEqual(observed[1], arguments)
			self.assertFalse(Path(temp, "injected").exists())
			self.assertEqual(json.loads((payload.parent / "status.json").read_text())["state"], "finished")

	def test_malformed_startup_status_is_rejected_before_tk(self):
		with tempfile.TemporaryDirectory() as temp:
			for value in ([], {"state": []}, {"state": {}}, {"state": "unknown"}, {"state": "running", "pid": True}, {"state": "finished", "pid": 1, "exit_code": "0"}):
				write_json(Path(temp, "status.json"), value)
				with self.assertRaises(LaunchError):
					session_status(temp)

	def test_launch_lock_refuses_simultaneous_helper(self):
		with tempfile.TemporaryDirectory() as temp:
			payload, plan = self.make_payload(temp, [])
			with computation_guard(payload, plan):
				with self.assertRaises(LaunchError):
					with computation_guard(payload, plan):
						self.fail("Acquired a duplicate computation lock")

	def test_duplicate_recheck_in_terminal_does_not_spawn_engine(self):
		with tempfile.TemporaryDirectory() as temp:
			payload, _ = self.make_payload(temp, [])
			with patch("gui_computation.duplicate_processes", return_value=([123], 0)), patch("gui_computation.subprocess.Popen") as spawn:
				self.assertEqual(run_computation(payload, pause=False), 1)
			spawn.assert_not_called()
			self.assertEqual(json.loads((payload.parent / "status.json").read_text())["state"], "failed")

	def test_computation_continues_after_launching_parent_exits(self):
		with tempfile.TemporaryDirectory() as temp:
			code = "from pathlib import Path; import time; Path('ready').touch();\nwhile not Path('finish').exists(): time.sleep(.05)"
			engine = Path(temp, "engine.py")
			engine.write_text(code)
			payload, _ = self.make_payload(temp, [str(engine)])
			shim = "import gui_computation as c; c.duplicate_processes=lambda p:([],0); c.run_computation(__import__('sys').argv[1],pause=False)"
			driver = "import subprocess,sys; p=subprocess.Popen([sys.executable,'-B','-c',sys.argv[1],sys.argv[2]],stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); print(p.pid)"
			parent = subprocess.run([sys.executable, "-B", "-c", driver, shim, str(payload)], cwd=ROOT, capture_output=True, text=True, check=True, timeout=10)
			self.assertTrue(parent.stdout.strip().isdigit())
			try:
				deadline = time.monotonic() + 10
				while not Path(temp, "ready").exists() and time.monotonic() < deadline:
					time.sleep(.02)
				self.assertTrue(Path(temp, "ready").exists())
				state = json.loads((payload.parent / "status.json").read_text())
				self.assertEqual(state["state"], "running")
			finally:
				Path(temp, "finish").touch()
				deadline = time.monotonic() + 5
				while time.monotonic() < deadline:
					if json.loads((payload.parent / "status.json").read_text()).get("state") == "finished":
						break
					time.sleep(.02)
				self.assertEqual(json.loads((payload.parent / "status.json").read_text())["state"], "finished")
