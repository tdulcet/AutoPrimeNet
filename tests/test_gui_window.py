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
from unittest.mock import patch


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
			if self.app.monitor.active:
				self.app.monitor.stop(force=True)
				self.wait_until(lambda: not self.app.monitor.active, timeout=10)
			self.wait_until(lambda: not self.app.jobs.busy, timeout=35)
			self.app.editor.dirty = False
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

	def test_advanced_dialog_cancel_apply_validation_and_reference(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n"
			path.write_text(original)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			window = editor.edit_options()
			editor.options_values["pm1_bounds"].set("MAX")
			window.destroy()
			self.assertFalse(editor.dirty)
			self.assertEqual(editor.values["pm1_bounds"].get(), "")
			self.app.search.set("--force-pminus1-bounds")
			row = self.app.reference.get_children()[0]
			self.assertIn("Optimal P−1 bounds", self.app.reference.item(row, "values")[2])
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			editor.options_values["convert_ll_to_prp"].set("True")
			editor.options_values["convert_prp_to_ll"].set("True")
			with patch("gui_forms.messagebox.showerror") as error:
				self.assertFalse(editor.apply_options())
				error.assert_called_once()
			self.assertFalse(editor.dirty)
			editor.options_values["convert_ll_to_prp"].set("False")
			editor.options_values["pm1_bounds"].set("MAX")
			self.assertTrue(editor.apply_options())
			self.assertTrue(editor.dirty)
			self.assertEqual(path.read_text(), original)
			with patch("autoprimenet_gui.messagebox.showinfo"), patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertFalse(editor.dirty)
			self.assertIn("pm1_bounds=MAX", path.read_text())
			self.app.search.set("ECM bounds multiplier")
			self.assertEqual(len(self.app.reference.get_children()), 1)

	def test_without_tray_close_keeps_reachable_minimized_window(self):
		self.root.update()
		self.app.hide()
		self.root.update()
		self.assertFalse(self.app.hidden)
		self.assertNotEqual(self.root.state(), "withdrawn")
		self.app.show()
		self.root.update()
		self.assertEqual(self.root.state(), "normal")

	def test_graphical_configuration_save_invalid_input_and_reload(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertIsNotNone(self.app.editor.document)
			self.app.editor.values["username"].set("ANONYMOUS")
			self.app.editor.engine.set("mlucas")
			self.app.editor.values["DaysOfWork"].set("nan")
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
				self.assertFalse((base / "prime.ini").exists())
				self.assertTrue(self.app.editor.dirty)
				self.app.editor.values["DaysOfWork"].set("2.5")
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertTrue((base / "prime.ini").is_file())
			self.assertFalse(self.app.editor.dirty)
			self.assertEqual(self.app.editor.document.config.getfloat("PrimeNet", "DaysOfWork"), 2.5)
			self.assertIn("saved locally", self.app.status.get())
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertEqual(self.app.editor.values["username"].get(), "ANONYMOUS")
			self.assertEqual({path.name for path in base.iterdir()}, {"prime.ini", "~lock", "~gui-monitor.lock"})

	def test_notifications_save_tls_conflict_reload_and_reference(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n[Email]\nfrom_email=sender@example.org\nsmtp_server=localhost\nusername=smtp-account\ntls=off\nstarttls=on\nsend=yes\n"
			path.write_text(original)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			values = self.app.editor.values
			self.assertEqual(values["username"].get(), "ANONYMOUS")

			self.assertEqual(values["email_username"].get(), "smtp-account")
			self.assertEqual(values["tls"].get(), "False")
			self.assertEqual(values["starttls"].get(), "True")
			self.assertEqual(values["notification_send"].get(), "True")
			self.app.search.set("--email-username")
			row = self.app.reference.get_children()[0]
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			self.assertEqual(self.app.notebook.select(), str(self.app.tabs["Notifications"]))
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				values["tls"].set("True")
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
				self.assertEqual(path.read_text(), original)
				self.assertIn("SSL/TLS or StartTLS", self.app.status.get())
				values["tls"].set("False")
				values["notification_send"].set("False")
				values["to_emails"].set("one@example.org, two@example.org")
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertFalse(self.app.editor.dirty)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertEqual(values["to_emails"].get(), "one@example.org,two@example.org")
			self.assertEqual(values["notification_send"].get(), "False")
			self.assertEqual(values["username"].get(), "ANONYMOUS")

	def test_hardware_dialog_cancel_reference_save_and_memory_conflict(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			window = editor.edit_options(group="Hardware")
			editor.options_values["memory"].set("8192")
			window.destroy()
			self.assertEqual(editor.values["memory"].get(), "")
			self.assertFalse(editor.dirty)
			self.app.search.set("--max-memory")
			row = self.app.reference.get_children()[0]
			self.assertIn("Hardware", self.app.reference.item(row, "values")[2])
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			self.assertEqual(self.app.notebook.select(), str(self.app.tabs["PrimeNet"]))
			self.root.update()
			self.assertEqual(len(editor.options_values), 11)
			editor.options_values["memory"].set("8192")
			editor.options_values["Memory"].set("16384")
			self.assertTrue(editor.apply_options())
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
				self.assertNotIn("Memory=", path.read_text())
				self.assertIn("Max memory", self.app.status.get())
				editor.edit_options(group="Hardware")
				editor.options_values["Memory"].set("4096")
				editor.options_values["WorkerDiskSpace"].set("2.5")
				self.assertTrue(editor.apply_options())
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertFalse(editor.dirty)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertEqual(editor.values["memory"].get(), "8192")
			self.assertEqual(editor.values["Memory"].get(), "4096")
			self.assertEqual(editor.values["WorkerDiskSpace"].get(), "2.5")
	def test_password_dialog_cancel_pending_edits_encrypted_save_and_remove(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n[Email]\nfrom_email=sender@example.org\nsmtp_server=localhost\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			editor.edit_passwords()
			editor.password_modes["email"].set("Replace")
			editor.password_values["email"].set("cancelled-fixture")
			editor.close_passwords()
			self.assertFalse(editor.dirty)
			self.assertEqual(editor.credentials, {})
			self.assertEqual(editor.password_values["email"].get(), "")
			self.app.search.set("--email-password")
			row = self.app.reference.get_children()[0]
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			self.assertEqual(self.app.notebook.select(), str(self.app.tabs["Notifications"]))
			editor.password_modes["email"].set("Replace")
			with patch("gui_forms.messagebox.showerror") as error:
				self.assertFalse(editor.apply_passwords())
				error.assert_called_once()
			editor.password_values["email"].set("desktop-mail-fixture")
			self.assertTrue(editor.apply_passwords())
			self.assertEqual(editor.credentials, {"email": "desktop-mail-fixture"})
			self.assertEqual(editor.password_values["email"].get(), "")
			editor.edit_passwords()
			self.assertEqual(editor.password_values["email"].get(), "")
			self.assertTrue(editor.apply_passwords())  # Keep retains the pending replacement.
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
			if "OpenSSL encryption is unavailable" in self.app.status.get():
				self.skipTest("Native OpenSSL encryption unavailable")
			self.assertFalse(editor.dirty)
			self.assertEqual(editor.credentials, {})
			self.assertIn("encrypted_password=", path.read_text())
			self.assertNotIn("desktop-mail-fixture", path.read_text())
			self.assertNotIn("desktop-mail-fixture", self.app.activity.get("1.0", "end") + self.app.status.get())
			editor.edit_passwords()
			editor.password_modes["email"].set("Remove")
			self.assertTrue(editor.apply_passwords())
			editor.edit_passwords()
			editor.password_modes["email"].set("Use saved")
			self.assertTrue(editor.apply_passwords())
			self.assertEqual(editor.credentials, {})
			editor.edit_passwords()
			editor.password_modes["email"].set("Remove")
			self.assertTrue(editor.apply_passwords())
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertNotIn("password=", path.read_text())

	def test_connection_dialog_proxy_validation_and_reference(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.search.set("--proxy-server")
			row = self.app.reference.get_children()[0]
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			editor = self.app.editor
			self.assertEqual(set(editor.options_values), {"proxy_type", "ProxyHost", "ProxyUser", "encrypt"})
			editor.options_values["proxy_type"].set("http")
			editor.options_values["ProxyHost"].set("localhost:8080")
			editor.options_values["ProxyUser"].set("fixture-proxy-user")
			editor.options_values["encrypt"].set("True")
			self.assertTrue(editor.apply_options())
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertFalse(editor.dirty)
			self.assertEqual(editor.document.config.get("PrimeNet", "ProxyUser"), "fixture-proxy-user")
			self.assertTrue(editor.document.config.getboolean("PrimeNet", "encrypt"))

	def test_unsaved_changes_can_cancel_reload_and_quit(self):
		with tempfile.TemporaryDirectory() as directory:
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.editor.values["username"].set("pending")
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=False):
				self.app.refresh()
				self.app.quit()
			self.assertFalse(self.app.closed)
			self.assertEqual(self.app.editor.values["username"].get(), "pending")
			self.assertFalse(self.app.jobs.busy)
			self.app.editor.dirty = False

	def test_scheduled_monitoring_controls_hide_and_confirmed_quit(self):
		from gui_controller import MonitorController
		from test_gui_monitor import fake_monitor_process

		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			content = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n"
			(base / "prime.ini").write_text(content)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.monitor = MonitorController(process_factory=fake_monitor_process)
			if sys.platform in {"darwin", "win32"}:
				self.app.tray.start()
				self.wait_until(lambda: self.app.tray.ready)
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.start_monitoring()
			self.wait_until(lambda: self.app.monitor.state == "Waiting")
			self.assertTrue(self.app.editor.widgets[0].instate(["disabled"]))
			self.assertTrue(self.app.save_button.instate(["disabled"]))
			self.app.hide()
			self.root.update()
			self.assertTrue(self.app.monitor.active)
			if self.app.tray.ready:
				self.assertEqual(self.root.state(), "withdrawn")
			self.app.show()
			self.assertIn("unverified", self.app.monitor_status.get())
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=False):
				self.app.quit()
			self.assertFalse(self.app.closed)
			self.assertTrue(self.app.monitor.active)
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.quit()
			self.wait_until(lambda: self.app.closed)
			self.assertFalse(self.app.monitor.active)
			self.assertEqual((base / "prime.ini").read_text(), content)

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
