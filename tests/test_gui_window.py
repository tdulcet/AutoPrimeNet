"""Opt-in desktop tests; never initialize Tk in a headless/default test run.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import os
from pathlib import Path
import sys
import tempfile
import time
import unittest


@unittest.skipUnless(os.environ.get("AUTOPRIMENET_GUI_DESKTOP_TESTS") == "1", "Requires an explicitly enabled graphical session")
class WindowTests(unittest.TestCase):
	def setUp(self):
		import tkinter as tk
		from autoprimenet_gui import Application

		self.root = tk.Tk()
		self.app = Application(self.root, tray=False)
		self.addCleanup(self.close_app)
		self.wait_until(lambda: not self.app.jobs.busy)

	def wait_until(self, predicate, timeout=15):
		deadline = time.monotonic() + timeout
		while not predicate() and time.monotonic() < deadline:
			self.root.update()
			time.sleep(0.02)
		self.assertTrue(predicate(), "Timed out waiting for desktop state")

	def close_app(self):
		if not self.app.closed:
			self.wait_until(lambda: not self.app.jobs.busy, timeout=35)
			self.app.quit()

	def test_navigation_search_workspace_and_repeated_refresh(self):
		self.assertEqual(len(self.app.notebook.tabs()), 8)
		for frame in self.app.tabs.values():
			self.app.notebook.select(frame)
			self.root.update()
		self.app.search.set("--password")
		self.assertEqual(len(self.app.reference.get_children()), 1)
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "prime.ini").write_text("[PrimeNet]\nmlucas=True\nusername=fixture-user\n")
			(base / "worktodo.txt").write_text("Test=127,70,1\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertIn("fixture-user", self.app.summary.get())
			self.assertEqual(len(self.app.assignments.get_children()), 1)
			self.assertIn("Unverified", self.app.assignments.item(self.app.assignments.get_children()[0])["values"])
			self.assertEqual({path.name for path in base.iterdir()}, {"prime.ini", "worktodo.txt"})

	def test_without_tray_close_keeps_reachable_minimized_window(self):
		self.root.update()
		self.app.hide()
		self.root.update()
		self.assertFalse(self.app.hidden)
		self.assertNotEqual(self.root.state(), "withdrawn")
		self.app.show()
		self.root.update()
		self.assertEqual(self.root.state(), "normal")

	@unittest.skipUnless(sys.platform == "darwin", "macOS application Quit command")
	def test_native_macos_quit_uses_application_cleanup(self):
		self.root.tk.call("tk::mac::Quit")
		self.assertTrue(self.app.closed)

	@unittest.skipUnless(sys.platform in {"darwin", "win32"}, "Native tray prototype currently supports macOS and Windows")
	def test_quit_stops_healthy_tray_helper(self):
		self.app.tray.start()
		self.wait_until(lambda: self.app.tray.ready)
		process = self.app.tray.process
		self.app.quit()
		self.assertEqual(process.wait(timeout=6), 0)

	@unittest.skipUnless(sys.platform in {"darwin", "win32"}, "Native tray prototype currently supports macOS and Windows")
	def test_tray_hide_restore_helper_failure_and_clean_shutdown(self):
		self.app.tray.start()
		self.wait_until(lambda: self.app.tray.ready)
		process = self.app.tray.process
		self.app.hide()
		self.assertTrue(self.app.hidden)
		self.assertEqual(self.root.state(), "withdrawn")
		self.app.tray.events.put("open")
		self.wait_until(lambda: not self.app.hidden)
		self.assertEqual(self.root.state(), "normal")
		self.app.hide()
		process.terminate()
		self.wait_until(lambda: not self.app.hidden and not self.app.tray.ready)
		self.assertEqual(self.root.state(), "normal")
		self.app.quit()
		process.wait(timeout=5)


if __name__ == "__main__":
	unittest.main()
