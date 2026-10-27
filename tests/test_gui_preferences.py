"""Workspace preference persistence and recovery regressions.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from gui_preferences import preferences_path, read_workspace, remember_workspace


class PreferencesTests(unittest.TestCase):
	def test_round_trip_and_private_file(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			path = base / "settings" / "preferences.json"
			document = SimpleNamespace(directory=base / "work space ü", path=base / "custom.ini")
			self.assertIsNone(read_workspace(path))
			remember_workspace(path, document)
			self.assertEqual(read_workspace(path), (str(document.directory), "custom.ini"))
			self.assertEqual(set(json.loads(path.read_text())), {"version", "directory", "config_name"})
			if os.name != "nt":
				self.assertEqual(path.stat().st_mode & 0o777, 0o600)

	def test_invalid_preferences(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "preferences.json"
			valid = {"version": 1, "directory": directory, "config_name": "prime.ini"}
			cases = [b"{", b"x" * 65537, b"null", b"[]"]
			for key, value in (("version", 2), ("directory", "relative"), ("directory", []), ("config_name", "../prime.ini"), ("config_name", ".")):
				cases.append(json.dumps({**valid, key: value}).encode())
			for data in cases:
				with self.subTest(data=data[:100]):
					path.write_bytes(data)
					with self.assertRaises(ValueError):
						read_workspace(path)

	def test_failed_write_preserves_previous_selection_and_cleans_temporary(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			path = base / "preferences.json"
			document = SimpleNamespace(directory=base, path=base / "prime.ini")
			remember_workspace(path, document)
			original = path.read_bytes()
			with patch("gui_preferences.os.replace", side_effect=OSError("fixture")):
				with self.assertRaises(OSError):
					remember_workspace(path, document)
			self.assertEqual(path.read_bytes(), original)
			self.assertEqual(list(base.iterdir()), [path])

	def test_platform_paths_and_relative_xdg_fallback(self):
		with tempfile.TemporaryDirectory() as directory:
			home = Path(directory)
			with patch("gui_preferences.Path.home", return_value=home), patch.dict("os.environ", {"APPDATA": str(home / "roaming"), "XDG_CONFIG_HOME": str(home / "xdg")}):
				for platform, base in (("win32", home / "roaming"), ("darwin", home / "Library" / "Application Support"), ("linux", home / "xdg")):
					with patch("gui_preferences.sys.platform", platform):
						self.assertEqual(preferences_path(), base / "AutoPrimeNetGUI" / "preferences.json")
				with patch("gui_preferences.sys.platform", "linux"), patch.dict("os.environ", {"XDG_CONFIG_HOME": "relative"}):
					self.assertEqual(preferences_path(), home / ".config" / "AutoPrimeNetGUI" / "preferences.json")
