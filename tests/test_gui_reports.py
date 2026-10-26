"""Read-only log snapshots and private diagnostic export tests.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument, WorkspaceError
from gui_reports import export_debug_report, read_backend_tail
from test_gui_monitor import fixture


class ReportTests(unittest.TestCase):
	def test_failed_export_does_not_leave_a_partial_private_report(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			with patch("gui_reports.backend_request", return_value={"text": "private fixture"}), patch("gui_reports.os.fsync", side_effect=OSError("fixture disk failure")):
				with self.assertRaises(OSError):
					export_debug_report(document)
			self.assertFalse(list(Path(directory).glob(".gui-debug-report-*")))
			self.assertEqual(document.path.read_bytes(), document.data)
	def test_backend_tail_is_bounded_and_preserves_original_bytes(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			path = Path(directory) / "autoprimenet.log"
			data = ("old-prefix\n" + "".join("record {:05d} contents\n".format(index) for index in range(10000))).encode()
			path.write_bytes(data)
			result = read_backend_tail(document)
			self.assertTrue(result["truncated"])
			self.assertLessEqual(len(result["text"].splitlines()), 2000)
			self.assertNotIn("old-prefix", result["text"])
			self.assertIn("record 09999 contents", result["text"])
			self.assertEqual(path.read_bytes(), data)

	def test_missing_symlink_and_directory_logs_are_refused(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			path = Path(directory) / "autoprimenet.log"
			with self.assertRaises(WorkspaceError):
				read_backend_tail(document)
			path.mkdir()
			with self.assertRaises(WorkspaceError):
				read_backend_tail(document)
			path.rmdir()
			target = Path(directory) / "target"
			target.write_text("private source")
			try:
				path.symlink_to(target)
			except OSError:
				return
			with self.assertRaises(WorkspaceError):
				read_backend_tail(document)
			self.assertEqual(target.read_text(), "private source")

	def test_native_debug_export_is_private_offline_and_contains_no_password(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			document.path.write_text(document.text + "ComputerGUID=" + "a" * 32 + "\n[Email]\nfrom_email=sender@example.org\nsmtp_server=localhost\npassword=fixture-secret-to-redact\n")
			document = ConfigDocument(directory)
			result = export_debug_report(document)
			path = Path(result["path"])
			self.assertIn("AutoPrimeNet version:", path.read_text())
			self.assertIn("Do not publicly post anything below this line", path.read_text())
			self.assertIn("a" * 32, path.read_text())
			self.assertNotIn("fixture-secret-to-redact", path.read_text())
			self.assertEqual(document.path.read_bytes(), document.data)
			self.assertEqual(len(list(Path(directory).iterdir())), 2)
			if os.name != "nt":
				self.assertEqual(path.stat().st_mode & 0o777, 0o600)

	def test_diagnostic_export_refuses_stale_config_and_oversize_response(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			with patch("gui_reports.backend_request", return_value={"text": "x" * (256 * 1024 + 1)}), self.assertRaises(WorkspaceError):
				export_debug_report(document)
			def changed(*_args, **_kwargs):
				document.path.write_text(document.text + "ComputerID=external-change\n")
				return {"text": "private report"}
			with patch("gui_reports.backend_request", side_effect=changed), self.assertRaisesRegex(WorkspaceError, "changed during diagnostics"):
				export_debug_report(document)
			self.assertFalse(list(Path(directory).glob(".gui-debug-report-*")))


if __name__ == "__main__":
	unittest.main()
