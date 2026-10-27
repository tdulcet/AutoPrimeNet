"""Local GUI workspace selection, separate from computation configuration.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import json
import os
from pathlib import Path
import sys
import tempfile


def preferences_path():
	if sys.platform == "win32":
		base = Path(os.environ.get("APPDATA") or Path.home() / "AppData" / "Roaming")
	elif sys.platform == "darwin":
		base = Path.home() / "Library" / "Application Support"
	else:
		configured = Path(os.environ.get("XDG_CONFIG_HOME", ""))
		base = configured if configured.is_absolute() else Path.home() / ".config"
	return base / "AutoPrimeNetGUI" / "preferences.json"


def read_workspace(path):
	try:
		with Path(path).open("rb") as stream:
			data = stream.read(65537)
	except FileNotFoundError:
		return None
	if len(data) > 65536:
		raise ValueError("GUI preferences are too large.")
	value = json.loads(data)
	if not isinstance(value, dict) or type(value.get("version")) is not int or value["version"] != 1:
		raise ValueError("Unsupported GUI preferences.")
	directory, name = value.get("directory"), value.get("config_name")
	if not isinstance(directory, str) or not directory or "\x00" in directory or not Path(directory).is_absolute():
		raise ValueError("Invalid remembered directory.")
	if not isinstance(name, str) or not name or Path(name).name != name or name in {".", ".."} or "\x00" in name:
		raise ValueError("Invalid remembered configuration filename.")
	return directory, name


def remember_workspace(path, document):
	path = Path(path)
	path.parent.mkdir(parents=True, exist_ok=True)
	data = json.dumps({"version": 1, "directory": str(document.directory), "config_name": document.path.name})
	temporary = None
	try:
		with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix=".preferences-", dir=path.parent, delete=False) as stream:
			temporary = stream.name
			stream.write(data)
			stream.flush()
			os.fsync(stream.fileno())
		os.replace(temporary, path)
	finally:
		if temporary is not None and Path(temporary).exists():
			Path(temporary).unlink()
