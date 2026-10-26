"""Safety tests for read-only workspace discovery.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from pathlib import Path
import os
import tempfile
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument, WorkspaceError, inspect_workspace, read_small_file, workspace_snapshot


class WorkspaceTests(unittest.TestCase):
	def test_preview_rejects_nonregular_and_oversized_files(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			with self.assertRaisesRegex(WorkspaceError, "regular file"):
				read_small_file(base)
			path = base / "large.txt"
			path.write_bytes(b"x" * (2 * 1024 * 1024 + 1))
			with self.assertRaisesRegex(WorkspaceError, "2 MiB"):
				read_small_file(path)
			(base / "worktodo.txt").mkdir()
			with self.assertRaisesRegex(WorkspaceError, "regular files"):
				inspect_workspace(directory)

	def test_replacement_between_stat_and_open_is_not_accepted(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=original\n")
			replacement = Path(directory) / "replacement.ini"
			replacement.write_text("[PrimeNet]\nusername=replaced\n")
			original_open = os.open
			def replace_then_open(target, flags, *args, **kwargs):
				replacement.replace(path)
				return original_open(target, flags, *args, **kwargs)
			with patch("gui_config.os.open", side_effect=replace_then_open):
				with self.assertRaisesRegex(WorkspaceError, "changed while opening"):
					ConfigDocument(directory)

	@unittest.skipUnless(hasattr(os, "mkfifo"), "Requires POSIX named pipes")
	def test_fifo_and_fifo_replacement_cannot_block_preview(self):
		# Run in a bounded subprocess: a regression must not hang the test suite.
		import subprocess
		import sys
		code = '''
import os, tempfile
from pathlib import Path
from unittest.mock import patch
from gui_config import ConfigDocument, WorkspaceError, read_small_file
with tempfile.TemporaryDirectory() as directory:
    path = Path(directory) / 'prime.ini'
    os.mkfifo(path)
    for read in (lambda: ConfigDocument(directory), lambda: read_small_file(path)):
        try: read()
        except WorkspaceError: pass
        else: raise AssertionError('FIFO accepted')
    path.unlink()
    path.write_text('[PrimeNet]\\n')
    original_open = os.open
    def replace(target, flags, *args, **kwargs):
        path.unlink()
        os.mkfifo(path)
        return original_open(target, flags, *args, **kwargs)
    with patch('gui_config.os.open', side_effect=replace):
        try: read_small_file(path)
        except WorkspaceError: pass
        else: raise AssertionError('FIFO replacement accepted')
'''
		result = subprocess.run([sys.executable, "-B", "-c", code], capture_output=True, text=True, timeout=5)
		self.assertEqual(result.returncode, 0, result.stderr)

	def test_preview_work_symlinks_remain_readable_but_config_links_refused(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			target = base / "target.txt"
			target.write_text("Test=127,70,1\n")
			link = base / "worktodo.txt"
			try:
				link.symlink_to(target)
			except OSError:
				self.skipTest("File symlinks unavailable")
			self.assertEqual(read_small_file(link), target.read_text())
			(base / "prime.ini").symlink_to(target)
			with self.assertRaisesRegex(WorkspaceError, "symbolic"):
				ConfigDocument(directory)

	def test_missing_config_does_not_create_runtime_files(self):
		with tempfile.TemporaryDirectory() as directory:
			snapshot = inspect_workspace(directory)
			self.assertFalse(snapshot["config_present"])
			self.assertEqual(snapshot["assignments"], [])
			self.assertEqual(list(Path(directory).iterdir()), [])

	def test_prpll_indexed_workers_and_secrets_excluded(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			config = "[PrimeNet]\nprpll=True\nNumWorkers=2\nusername=tester\nProxyPass=secret-proxy\n[Email]\npassword=secret-mail\n"
			(base / "prime.ini").write_text(config)
			(base / "worktodo-0.txt").write_text("Test=127,70,1\n")
			(base / "worktodo-1.txt").write_text("PRP=1,2,131,-1,70,1.3\n")
			before = {path.name: path.read_bytes() for path in base.iterdir()}
			snapshot = inspect_workspace(directory)
			self.assertEqual([item["worker"] for item in snapshot["assignments"]], [1, 2])
			self.assertEqual(snapshot["identity"]["username"], "tester")
			self.assertNotIn("secret-", str(snapshot))
			self.assertEqual(before, {path.name: path.read_bytes() for path in base.iterdir()})

	def test_duplicate_and_symlink_worker_directories_rejected(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "worker").mkdir()
			try:
				(base / "alias").symlink_to(base / "worker", target_is_directory=True)
			except OSError:
				self.skipTest("Directory symlinks unavailable")
			(base / "prime.ini").write_text("[PrimeNet]\nmlucas=True\nNumWorkers=2\n[Worker #1]\ndirectory=worker\n[Worker #2]\ndirectory=alias\n")
			with self.assertRaisesRegex(WorkspaceError, "same location"):
				workspace_snapshot(directory)

	def test_conflicting_engines_invalid_counts_paths_and_interpolation(self):
		for content in (
			"[PrimeNet]\nmlucas=True\nprpll=True\n",
			"[PrimeNet]\nNumWorkers=0\n",
			"[PrimeNet]\nwork_file=../worktodo.txt\n",
			"[PrimeNet]\nusername=broken%value\n",
			"[PrimeNet]\nNumWorkers=2\n",
		):
			with self.subTest(content=content), tempfile.TemporaryDirectory() as directory:
				(Path(directory) / "prime.ini").write_text(content)
				with self.assertRaises(WorkspaceError):
					workspace_snapshot(directory)

	def test_custom_config_name_and_case_sensitive_unknown_values_preserved(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "custom.ini"
			content = "[PrimeNet]\nusername=proper\nUsername=other\n[Unknown]\nKeep=100%\n"
			path.write_text(content)
			snapshot = workspace_snapshot(directory, "custom.ini")
			self.assertEqual(snapshot["identity"]["username"], "proper")
			self.assertEqual(path.read_text(), content)
			with self.assertRaises(WorkspaceError):
				workspace_snapshot(directory, "../custom.ini")


if __name__ == "__main__":
	unittest.main()
