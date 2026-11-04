"""Independent terminal computation launcher; never owned by GUI shutdown.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from contextlib import contextmanager
import base64
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time
import uuid

from gui_launch_profiles import LaunchError, TERMINALS, defaults, file_lock, load_settings, read_bytes, validate_settings, write_json
from gui_progress import identify_engine


ROOT = Path(__file__).resolve().parent
SESSION_DIRECTORY = ".autoprimenet-gui-launches"
# Terminal receives only the trusted Python helper and payload path. Engine
# arguments remain a JSON array and are never interpolated into shell commands.
APPLE_SCRIPT = '''on run argv
 tell application "Terminal"
  activate
  do script (item 1 of argv)
 end tell
end run'''


def resolve_profile(base, profile):
	validate_settings({**defaults(), "profiles": [profile]})
	base = Path(base).resolve(strict=True)
	directory = (base / Path(profile["directory"]).expanduser()).resolve(strict=True)
	if not directory.is_dir():
		raise LaunchError("The computation working directory does not exist.")
	name = os.path.expanduser(profile["executable"])
	if Path(name).is_absolute() or "/" in name or "\\" in name:
		executable = (base / name).resolve(strict=True)
	else:
		found = shutil.which(name)
		if not found:
			raise LaunchError("The computation executable was not found. Browse to its installed file.")
		executable = Path(found).resolve(strict=True)
	if not executable.is_file() or (os.name != "nt" and not os.access(executable, os.X_OK)):
		raise LaunchError("Select an executable computation program.")
	if os.name == "nt" and executable.suffix.lower() not in {".exe", ".com"}:
		raise LaunchError("Select the engine's .exe or .com binary, rather than a shell script.")
	return {"name": profile["name"], "program": profile["program"], "directory": str(directory),
		"argv": [str(executable), *profile["arguments"]], "terminal": profile["terminal"]}


def duplicate_processes(plan):
	import psutil
	matches, inaccessible = [], 0
	for process in psutil.process_iter():
		if process.pid == os.getpid():
			continue
		try:
			engine = identify_engine(process.name())
			try:
				same_executable = Path(process.exe()).resolve() == Path(plan["argv"][0]).resolve()
			except psutil.AccessDenied:
				inaccessible += 1
				same_executable = False
			if not same_executable and engine != plan["program"]:
				continue
			if Path(process.cwd()).resolve() == Path(plan["directory"]).resolve():
				matches.append(process.pid)
		except psutil.AccessDenied:
			inaccessible += 1
		except (psutil.NoSuchProcess, psutil.ZombieProcess):
			continue
	return matches, inaccessible


def select_terminal(preference, platform=None, which=None):
	platform, which = platform or sys.platform, which or shutil.which
	if preference not in TERMINALS:
		raise LaunchError("Unknown terminal preference.")
	if platform == "darwin":
		if preference not in {"auto", "Terminal"}:
			raise LaunchError("Choose auto or Terminal on macOS.")
		if not which("osascript"):
			raise LaunchError("macOS Terminal automation is unavailable (osascript missing).")
		return "Terminal", which("osascript")
	if platform == "win32":
		choices = ("PowerShell", "Cmd") if preference == "auto" else (preference,)
		for name in choices:
			candidates = ("pwsh.exe", "powershell.exe") if name == "PowerShell" else ("cmd.exe",) if name == "Cmd" else ()
			for candidate in candidates:
				if found := which(candidate):
					return name, found
	else:
		choices = ("ptyxis", "gnome-terminal", "konsole", "xfce4-terminal", "xterm") if preference == "auto" else (preference,)
		for name in choices:
			if name in {"ptyxis", "gnome-terminal", "konsole", "xfce4-terminal", "xterm"} and (found := which(name)):
				return name, found
	raise LaunchError("The selected terminal is unavailable. Install or select a supported terminal.")


def prepare_launch(base, profile, expected):
	_, current = load_settings(base)
	if current != expected:
		raise LaunchError("Launcher settings changed. Reload launchers before starting computation.")
	plan = resolve_profile(base, profile)
	name, executable = select_terminal(plan["terminal"])
	matches, inaccessible = duplicate_processes(plan)
	if matches:
		raise LaunchError("A matching computation program is already running in this directory (PID(s): " + ", ".join(map(str, matches)) + "). Stop this worker in terminal.")
	return {"plan": plan, "terminal": name, "terminal_executable": executable, "inaccessible": inaccessible}


def console_python():
	executable = Path(sys.executable)
	if sys.platform == "win32" and executable.name.casefold() == "pythonw.exe":
		executable = executable.with_name("python.exe")
		if not executable.is_file():
			raise LaunchError("A console-capable python.exe is required next to pythonw.exe.")
	return str(executable)


def terminal_command(kind, executable, payload, python=None, platform=None):
	python, platform = python or console_python(), platform or sys.platform
	command = [python, "-B", str(ROOT / "gui_computation.py"), "--run", str(payload)]
	kwargs = {"close_fds": True}
	if platform != "win32":
		kwargs["start_new_session"] = True
	if kind == "Terminal":
		return [executable, "-e", APPLE_SCRIPT, shlex.join(command)], kwargs
	if kind == "PowerShell":
		quoted = " & " + " ".join("'" + argument.replace("'", "''") + "'" for argument in command)
		encoded = base64.b64encode(quoted.encode("utf-16-le")).decode("ascii")
		kwargs["creationflags"] = getattr(subprocess, "CREATE_NEW_CONSOLE", 0x10)
		return [executable, "-NoLogo", "-NoProfile", "-NoExit", "-EncodedCommand", encoded], kwargs
	if kind == "Cmd":
		kwargs["creationflags"] = getattr(subprocess, "CREATE_NEW_CONSOLE", 0x10)
		# A static script avoids cmd.exe /K quoting of dynamic paths. Expansion
		# occurs once, with delayed expansion disabled, inside quoted operands.
		kwargs["cwd"] = str(Path(payload).parent)
		kwargs["env"] = {**os.environ, "APN_GUI_PYTHON": python, "APN_GUI_HELPER": str(ROOT / "gui_computation.py"),
			"APN_GUI_PAYLOAD": str(payload)}
		return [executable, "/D", "/V:OFF", "/K", "launch.cmd"], kwargs
	prefix = {"ptyxis": ["--standalone", "--"], "gnome-terminal": ["--"], "konsole": ["--separate", "-e"],
		"xfce4-terminal": ["--disable-server", "--execute"], "xterm": ["-e"]}
	if kind not in prefix:
		raise LaunchError("Unsupported terminal.")
	return [executable, *prefix[kind], *command], kwargs


def launch_computation(base, profile, expected):
	prepared = prepare_launch(base, profile, expected)
	root = Path(base).resolve() / SESSION_DIRECTORY
	if root.is_symlink():
		raise LaunchError("The GUI launch-session directory must not be a symbolic link.")
	root.mkdir(mode=0o700, exist_ok=True)
	session = root / uuid.uuid4().hex
	session.mkdir(mode=0o700)
	payload = session / "launch.json"
	write_json(payload, prepared["plan"])
	write_json(session / "status.json", {"state": "waiting", "time": time.time()})
	# The helper waits in an independent terminal; GUI exit never stops it.
	if prepared["terminal"] == "Cmd":
		with (session / "launch.cmd").open("w", encoding="ascii", newline="") as stream:
			stream.write('@echo off\r\nsetlocal DisableDelayedExpansion\r\n"%APN_GUI_PYTHON%" -B "%APN_GUI_HELPER%" --run "%APN_GUI_PAYLOAD%"\r\n')
	argv, kwargs = terminal_command(prepared["terminal"], prepared["terminal_executable"], payload)
	try:
		if sys.platform != "win32":
			kwargs.update(stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
		process = subprocess.Popen(argv, **kwargs)
		# Reap only the terminal-invocation child; never attach a stop handler.
		import threading
		def reap():
			code = process.wait()
			if code:
				try:
					if session_status(session)["state"] == "waiting":
						write_json(session / "status.json", {"state": "failed", "reason": "terminal", "time": time.time()})
				except (OSError, ValueError):
					pass
		threading.Thread(target=reap, daemon=True, name="Computation terminal").start()
	except OSError as error:
		write_json(session / "status.json", {"state": "failed", "time": time.time()})
		raise LaunchError("The terminal could not be opened. Check the saved terminal preference.") from error
	return {"session": str(session), "name": profile["name"], "directory": str(Path(base).resolve())}


def session_status(session):
	value = json.loads(read_bytes(Path(session) / "status.json", 8192))
	if not isinstance(value, dict) or value.get("state") not in {"waiting", "running", "finished", "failed"}:
		raise LaunchError("Invalid computation startup status.")
	if value["state"] in {"running", "finished"} and (type(value.get("pid")) is not int or value["pid"] < 1):
		raise LaunchError("Invalid computation PID.")
	if value["state"] == "finished" and type(value.get("exit_code")) is not int:
		raise LaunchError("Invalid computation exit status.")
	return value


@contextmanager
def computation_guard(payload, plan):
	key = hashlib.sha256(json.dumps([plan["argv"][0], plan["directory"]]).encode()).hexdigest()
	path = Path(payload).parent.parent / (key + ".lock")
	with file_lock(path):
		yield


def publish_status(path, value):
	# Status is informational. A full/read-only disk must not abandon an
	# already-started engine or release its launch guard before it exits.
	try:
		write_json(path, value)
	except (OSError, ValueError):
		print("GUI status could not be saved; check this terminal for computation state.", file=sys.stderr, flush=True)


def run_computation(payload, pause=True):
	payload = Path(payload).resolve(strict=True)
	status = payload.parent / "status.json"
	try:
		plan = json.loads(read_bytes(payload))
		# Revalidate data in the terminal. No shells interpret engine arguments.
		profile = {"name": plan["name"], "program": plan["program"], "directory": plan["directory"],
			"executable": plan["argv"][0], "arguments": plan["argv"][1:], "terminal": plan["terminal"]}
		plan = resolve_profile(payload.parent, profile)
		with computation_guard(payload, plan):
			matches, _ = duplicate_processes(plan)
			if matches:
				raise LaunchError("A matching computation is already running in the selected directory. Stop this worker in terminal.")
			print("Starting " + plan["name"] + " in " + plan["directory"], flush=True)
			process = subprocess.Popen(plan["argv"], cwd=plan["directory"])
			publish_status(status, {"state": "running", "pid": process.pid, "time": time.time()})
			code = process.wait()
			publish_status(status, {"state": "finished", "pid": process.pid, "exit_code": code, "time": time.time()})
			print("\nComputation exited with status " + str(code) + ".", flush=True)
	except Exception as error:
		publish_status(status, {"state": "failed", "time": time.time()})
		print("Unable to start computation: " + str(error), file=sys.stderr, flush=True)
		code = 1
	if pause:
		try:
			input("Press Enter to close this computation session…")
		except (EOFError, KeyboardInterrupt):
			pass
	return code


if __name__ == "__main__":
	if len(sys.argv) != 3 or sys.argv[1] != "--run":
		raise SystemExit("This helper is started by the GUI's computation launcher.")
	raise SystemExit(run_computation(sys.argv[2]))
