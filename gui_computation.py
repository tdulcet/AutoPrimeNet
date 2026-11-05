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
import stat
import subprocess
import tempfile
import sys
import time
import uuid

from gui_progress import ENGINES, REPORT_ONLY, identify_engine

FILENAME = "autoprimenet-gui-launchers.json"
PROFILE_LOCK = ".autoprimenet-gui-launchers.lock"
PROGRAMS = (*ENGINES, *REPORT_ONLY)
TERMINALS = ("auto", "Terminal", "PowerShell", "Cmd", "ptyxis", "gnome-terminal", "konsole", "xfce4-terminal", "xterm")
MAX_BYTES = 128 * 1024


class LaunchError(ValueError):
	"""A readable launch/profile error."""


def defaults():
	return {"version": 1, "refresh_seconds": 90, "profiles": []}


def clean_text(value, label, empty=False):
	if not isinstance(value, str) or (not value and not empty) or len(value) > 4096 or any(char in value for char in "\x00\r\n"):
		raise LaunchError(label + " must be a single line of at most 4096 characters.")
	return value


def validate_settings(value):
	if not isinstance(value, dict) or set(value) != {"version", "refresh_seconds", "profiles"} or type(value["version"]) is not int or value["version"] != 1:
		raise LaunchError("Unsupported launcher settings format.")
	if type(value["refresh_seconds"]) is not int or not 1 <= value["refresh_seconds"] <= 86400:
		raise LaunchError("Progress refresh must be 1–86400 seconds.")
	profiles = value["profiles"]
	if not isinstance(profiles, list) or len(profiles) > 128:
		raise LaunchError("A workspace supports at most 128 launch profiles.")
	names = set()
	for profile in profiles:
		if not isinstance(profile, dict) or set(profile) != {"name", "program", "executable", "directory", "arguments", "terminal"}:
			raise LaunchError("Invalid launch profile fields.")
		for key in ("name", "program", "executable", "directory", "terminal"):
			clean_text(profile[key], key, empty=key == "directory")
		if len(profile["name"]) > 80 or profile["name"].casefold() in names:
			raise LaunchError("Profile names must be unique and at most 80 characters.")
		names.add(profile["name"].casefold())
		if profile["program"] not in PROGRAMS or profile["terminal"] not in TERMINALS:
			raise LaunchError("Choose a supported computation program and terminal.")
		arguments = profile["arguments"]
		if not isinstance(arguments, list) or len(arguments) > 128:
			raise LaunchError("Use at most 128 arguments, one per line.")
		for argument in arguments:
			clean_text(argument, "Argument", empty=True)
	return value


def read_bytes(path, limit=MAX_BYTES):
	path = Path(path)
	before = path.lstat()
	if not stat.S_ISREG(before.st_mode):
		raise LaunchError("Launcher files must be regular files, not symbolic links.")
	flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_BINARY", 0)
	with os.fdopen(os.open(path, flags), "rb") as stream:
		info = os.fstat(stream.fileno())
		if not stat.S_ISREG(info.st_mode) or (before.st_dev, before.st_ino) != (info.st_dev, info.st_ino):
			raise LaunchError("Launcher file changed while opening; reload it.")
		data = stream.read(limit + 1)
	if len(data) > limit:
		raise LaunchError("Launcher file exceeds its size limit.")
	return data


def load_settings(directory):
	try:
		data = read_bytes(Path(directory) / FILENAME)
	except FileNotFoundError:
		return defaults(), None
	try:
		value = json.loads(data)
	except (UnicodeError, ValueError) as error:
		raise LaunchError("Launcher settings are malformed; repair or move the file before saving.") from error
	return validate_settings(value), hashlib.sha256(data).hexdigest()


def write_json(path, value):
	path = Path(path)
	encoded = json.dumps(value, ensure_ascii=True, indent=2) + "\n"
	if len(encoded.encode("utf-8")) > MAX_BYTES:
		raise LaunchError("Launcher file exceeds 128 KiB.")
	temporary = None
	try:
		with tempfile.NamedTemporaryFile("w", encoding="utf-8", prefix=".launcher-", dir=path.parent, delete=False) as stream:
			temporary = Path(stream.name)
			stream.write(encoded)
			stream.flush()
			os.fsync(stream.fileno())
		os.replace(temporary, path)
	finally:
		if temporary is not None:
			temporary.unlink(missing_ok=True)


@contextmanager
def file_lock(path):
	path = Path(path)
	flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_BINARY", 0)
	with os.fdopen(os.open(path, flags, 0o600), "r+b", buffering=0) as stream:
		info, linked = os.fstat(stream.fileno()), path.lstat()
		if not stat.S_ISREG(info.st_mode) or not stat.S_ISREG(linked.st_mode) or (info.st_dev, info.st_ino) != (linked.st_dev, linked.st_ino):
			raise LaunchError("Launcher lock must be a regular, non-symlink file.")
		try:
			if os.name == "nt":
				import msvcrt
				if not info.st_size:
					stream.write(b"0")
					stream.flush()
				stream.seek(0)
				msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
			else:
				import fcntl
				fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
		except OSError as error:
			raise LaunchError("Another launcher operation or computation holds this lock. Try again after it finishes.") from error
		try:
			yield
		finally:
			if os.name == "nt":
				stream.seek(0)
				msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)


def save_settings(directory, value, expected):
	validate_settings(value)
	if len((json.dumps(value, ensure_ascii=True, indent=2) + "\n").encode("utf-8")) > MAX_BYTES:
		raise LaunchError("Launcher settings exceed 128 KiB.")
	with file_lock(Path(directory) / PROFILE_LOCK):
		_, current = load_settings(directory)
		if current != expected:
			raise LaunchError("Launcher settings changed externally. Reload launchers before saving.")
		write_json(Path(directory) / FILENAME, value)
		return load_settings(directory)


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
	info = executable.stat()
	return {"name": profile["name"], "program": profile["program"], "directory": str(directory),
		"executable_id": [info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns],
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


def plan_digest(plan):
	return hashlib.sha256(json.dumps(plan, sort_keys=True).encode("utf-8")).hexdigest()


def terminal_command(kind, executable, payload, digest, python=None, platform=None):
	python, platform = python or console_python(), platform or sys.platform
	command = [python, "-B", str(ROOT / "gui_computation.py"), "--run", digest, str(payload)]
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
			"APN_GUI_PAYLOAD": str(payload), "APN_GUI_DIGEST": digest}
		return [executable, "/D", "/V:OFF", "/K", "launch.cmd"], kwargs
	prefix = {"ptyxis": ["--standalone", "--"], "gnome-terminal": ["--"], "konsole": ["--separate", "-e"],
		"xfce4-terminal": ["--disable-server", "--execute"], "xterm": ["-e"]}
	if kind not in prefix:
		raise LaunchError("Unsupported terminal.")
	return [executable, *prefix[kind], *command], kwargs


def launch_computation(base, profile, expected, reviewed):
	prepared = prepare_launch(base, profile, expected)
	if any(prepared[key] != reviewed[key] for key in ("plan", "terminal", "terminal_executable")):
		raise LaunchError("The launch target changed after review. Review the profile again before starting.")
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
			stream.write('@echo off\r\nsetlocal DisableDelayedExpansion\r\n"%APN_GUI_PYTHON%" -B "%APN_GUI_HELPER%" --run "%APN_GUI_DIGEST%" "%APN_GUI_PAYLOAD%"\r\n')
	argv, kwargs = terminal_command(prepared["terminal"], prepared["terminal_executable"], payload, plan_digest(reviewed["plan"]))
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
	if not isinstance(value, dict) or not isinstance(value.get("state"), str) or value["state"] not in {"waiting", "running", "finished", "failed"}:
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


def run_computation(payload, pause=True, expected_digest=None):
	payload = Path(payload).resolve(strict=True)
	status = payload.parent / "status.json"
	try:
		plan = json.loads(read_bytes(payload))
		if expected_digest is not None and plan_digest(plan) != expected_digest:
			raise LaunchError("The launch request no longer matches the reviewed profile.")
		# Revalidate data in the terminal. No shells interpret engine arguments.
		profile = {"name": plan["name"], "program": plan["program"], "directory": plan["directory"],
			"executable": plan["argv"][0], "arguments": plan["argv"][1:], "terminal": plan["terminal"]}
		with computation_guard(payload, plan):
			matches, _ = duplicate_processes(plan)
			if matches:
				raise LaunchError("A matching computation is already running in the selected directory. Stop this worker in terminal.")
			print("Starting " + plan["name"] + " in " + plan["directory"], flush=True)
			if resolve_profile(payload.parent, profile) != plan:
				raise LaunchError("The reviewed executable or directory changed before startup.")
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
	if len(sys.argv) != 4 or sys.argv[1] != "--run":
		raise SystemExit("This helper is started by the GUI's computation launcher.")
	raise SystemExit(run_computation(sys.argv[3], expected_digest=sys.argv[2]))
