"""Workspace-local computation launch profiles and Progress preferences.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile

from gui_progress import ENGINES, REPORT_ONLY


FILENAME = "autoprimenet-gui-launchers.json"
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
			# Closing releases the POSIX lock; retain its inode for other clients.


def save_settings(directory, value, expected):
	validate_settings(value)
	if len((json.dumps(value, ensure_ascii=True, indent=2) + "\n").encode("utf-8")) > MAX_BYTES:
		raise LaunchError("Launcher settings exceed 128 KiB.")
	with file_lock(Path(directory) / ".autoprimenet-gui-launchers.lock"):
		_, current = load_settings(directory)
		if current != expected:
			raise LaunchError("Launcher settings changed externally. Reload launchers before saving.")
		write_json(Path(directory) / FILENAME, value)
		return load_settings(directory)
