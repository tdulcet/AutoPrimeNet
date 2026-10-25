"""Safety tests for read-only workspace discovery.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from pathlib import Path
import tempfile
import unittest

from gui_config import WorkspaceError, inspect_workspace, workspace_snapshot


class WorkspaceTests(unittest.TestCase):
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
