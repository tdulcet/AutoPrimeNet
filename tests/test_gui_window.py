"""Opt-in desktop tests; never initialize Tk in a headless/default test run.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import os
import importlib.util
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch


def native_tray_installed():
	return all(importlib.util.find_spec(name) is not None for name in ("pystray", "PIL"))


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
			self.app.registration.close()
			self.app.quit()

	def test_quit_cancels_pending_poll_callback(self):
		pending = self.app.poll_after
		self.assertIsNotNone(pending)
		self.assertIn(pending, self.root.tk.call("after", "info"))
		self.app.quit()
		self.assertTrue(self.app.closed)
		self.assertIsNone(self.app.poll_after)
		self.assertNotIn(pending, self.root.tk.call("after", "info"))

	def test_reload_closes_old_dialogs_and_clears_unapplied_passwords(self):
		from gui_config import ConfigDocument
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			for kind in ("options", "passwords", "mail", "worker"):
				with self.subTest(dialog=kind):
					if kind == "options":
						window = editor.edit_options(group="Hardware")
						editor.options_values["CpuBrand"].set("old draft")
					elif kind == "passwords":
						window = editor.edit_passwords()
						editor.password_values["email"].set("unapplied-private-fixture")
					elif kind == "mail":
						window = editor.discover_mail()
					else:
						self.app.workers.selection_set(self.app.workers.get_children()[0])
						editor.edit_worker()
						window = editor.worker_window
					editor.load(ConfigDocument(directory))
					self.assertFalse(window.winfo_exists())
					self.assertEqual(editor.credentials, {})
					self.assertEqual(editor.values["CpuBrand"].get(), "")
					if kind == "passwords":
						self.assertEqual(editor.password_values["email"].get(), "")

	def test_failed_directory_change_preserves_unsaved_settings(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			document = self.app.editor.document
			self.app.editor.values["ComputerID"].set("unsaved-fixture")
			with patch("autoprimenet_gui.filedialog.askdirectory", return_value=str(Path(directory) / "missing")), patch("autoprimenet_gui.messagebox.askyesno", return_value=True) as confirm:
				self.app.choose_directory()
				self.wait_until(lambda: not self.app.jobs.busy)
				confirm.assert_called_once()
			self.assertIs(self.app.editor.document, document)
			self.assertTrue(self.app.editor.dirty)
			self.assertEqual(self.app.editor.values["ComputerID"].get(), "unsaved-fixture")

	def test_directory_change_confirms_queued_batch_discard_only_once(self):
		with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
			for directory in (first, second):
				(Path(directory) / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(first)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			window = self.app.registration.open()
			self.app.registration.values["exponent"].set("127")
			self.app.registration.add()
			with patch("autoprimenet_gui.filedialog.askdirectory", return_value=second), patch("autoprimenet_gui.messagebox.askyesno", return_value=True) as confirm:
				self.app.choose_directory()
				self.wait_until(lambda: not self.app.jobs.busy)
				confirm.assert_called_once()
			self.assertEqual(self.app.editor.document.directory, Path(second).resolve())
			self.assertFalse(window.winfo_exists())

	def test_gpu_discovery_review_cancel_and_staged_apply(self):
		from gui_hardware import gpu_settings
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n"
			path.write_text(original)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			target = editor.edit_options(group="Hardware")
			settings = gpu_settings(("Fixture GPU", 24, 1500, 64, 512, 8192, "ARCH=SM80", "CUDA"))
			result = {"devices": [{"name": "Fixture GPU", "source": "CUDA", "settings": settings}]}
			with patch("gui_forms.backend_request", return_value=result):
				editor.discover_gpus()
				self.wait_until(lambda: not self.app.jobs.busy)
			picker = next(child for child in target.winfo_children() if child.winfo_class() == "Toplevel")
			def descendants(widget):
				return [child for child in widget.winfo_children() for child in [child, *descendants(child)]]
			controls = descendants(picker)
			selector = next(widget for widget in controls if widget.winfo_class() == "TCombobox")
			selector.current(0)
			selector.event_generate("<<ComboboxSelected>>")
			next(widget for widget in controls if widget.winfo_class() == "TButton" and widget.cget("text") == "Use in hardware dialog").invoke()
			self.assertEqual(editor.options_values["CpuBrand"].get(), "Fixture GPU")
			self.assertEqual(editor.values["CpuBrand"].get(), "")
			self.assertFalse(editor.dirty)
			self.assertTrue(editor.apply_options())
			self.assertEqual(editor.values["CpuBrand"].get(), "Fixture GPU")
			self.assertTrue(editor.dirty)
			self.assertEqual(path.read_text(), original)
			# A result arriving after its target closes must not touch a new dialog.
			old = editor.edit_options(group="Hardware")
			editor.gpu_target = old
			old.destroy()
			new = editor.edit_options(group="Hardware")
			editor.complete_gpus(result, None)
			self.assertFalse(any(child.winfo_class() == "Toplevel" for child in new.winfo_children()))
			new.destroy()

	def test_gpu_discovery_empty_failure_and_picker_cancel_preserve_settings(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nCpuBrand=Existing CPU\n"
			path.write_text(original)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			target = editor.edit_options(group="Hardware")
			with patch("gui_forms.messagebox.showinfo") as info:
				editor.gpu_target = target
				editor.complete_gpus({"devices": []}, None)
				info.assert_called_once()
			with patch("gui_forms.messagebox.showerror") as error:
				editor.gpu_target = target
				editor.complete_gpus(None, RuntimeError("private driver output"))
				error.assert_called_once()
				self.assertNotIn("private driver output", str(error.call_args))
			editor.gpu_target = target
			editor.complete_gpus({"devices": [{"name": "GPU", "source": "CUDA", "settings": {"CpuBrand": "GPU"}}]}, None)
			picker = next(child for child in target.winfo_children() if child.winfo_class() == "Toplevel")
			picker.event_generate("<Escape>")
			self.root.update()
			# Closing either dialog does not apply discovered values.
			target.destroy()
			self.assertEqual(editor.values["CpuBrand"].get(), "Existing CPU")
			self.assertFalse(editor.dirty)
			self.assertEqual(path.read_text(), original)

	def test_mail_discovery_confirmation_review_apply_and_preservation(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n[Email]\nfrom_email=User <user@example.com>\npassword=old-secret\nsend=False\n"
			path.write_text(original)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			editor.discover_mail()
			result = {"match": {"provider": "Fixture", "security": "STARTTLS", "settings": {"smtp_server": "smtp.example.com:587", "tls": "False", "starttls": "True", "email_username": "user@example.com"}}}
			with patch("gui_forms.messagebox.askyesno", return_value=False), patch("gui_forms.discover_mail") as lookup:
				editor.start_mail_lookup()
				lookup.assert_not_called()
			self.assertFalse(editor.dirty)
			with patch("gui_forms.messagebox.askyesno", return_value=True), patch("gui_forms.discover_mail", return_value=result) as lookup:
				editor.start_mail_lookup()
				self.wait_until(lambda: not self.app.jobs.busy)
				lookup.assert_called_once_with(editor.document, "user@example.com")
			self.assertEqual(editor.values["smtp_server"].get(), "")
			self.assertIn("smtp.example.com:587", editor.mail_details.get())
			self.assertFalse(editor.dirty)
			editor.apply_mail()
			self.assertTrue(editor.dirty)
			self.assertEqual(editor.values["smtp_server"].get(), "smtp.example.com:587")
			self.assertEqual(editor.values["notification_send"].get(), "False")
			self.assertEqual(editor.credentials, {})
			self.assertEqual(path.read_text(), original)

	def test_mail_discovery_address_change_cancel_empty_and_failure(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			editor = self.app.editor
			window = editor.discover_mail()
			editor.mail_address.set("user@example.com")
			result = {"match": {"provider": "Fixture", "security": "SSL", "settings": {"smtp_server": "smtp.example.com:465", "tls": "True", "starttls": "False"}}}
			with patch("gui_forms.messagebox.askyesno", return_value=True), patch("gui_forms.discover_mail", return_value=result):
				editor.start_mail_lookup()
				self.wait_until(lambda: not self.app.jobs.busy)
			editor.mail_address.set("other@example.com")
			editor.apply_mail()
			self.assertIn("changed", editor.mail_details.get())
			self.assertFalse(editor.dirty)
			editor.mail_address.set("user@example.com")
			editor.complete_mail({"match": None}, None)
			self.assertIn("No provider", editor.mail_details.get())
			editor.complete_mail(None, RuntimeError("private error"))
			self.assertNotIn("private error", editor.mail_details.get())
			window.destroy()
			editor.complete_mail(result, None)
			self.assertFalse(editor.dirty)

	def test_polling_and_watching_are_reachable_and_saved_from_forms(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nHoursBetweenCheckins=2\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.search.set("--timeout")
			row = self.app.reference.get_children()[0]
			self.assertEqual(self.app.reference.item(row, "values")[-1], "Available")
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			editor = self.app.editor
			self.assertTrue(editor.options_window.winfo_exists())
			editor.options_values["poll_seconds"].set("1800")
			editor.options_values["watch"].set("False")
			self.assertTrue(editor.apply_options())
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertFalse(editor.dirty)
			self.assertEqual(editor.document.config.getint("GUI", "PollSeconds"), 1800)
			self.assertFalse(editor.document.config.getboolean("PrimeNet", "watch"))

	def test_debug_controls_confirmation_and_private_trace_viewer(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n[GUI]\nDebugLevel=2\n")
			(base / ".gui-backend-trace-fixture.log").write_text("fixture-private-password")
			(base / "autoprimenet.log").write_text("fixture-native-log")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=False) as confirm:
				self.app.start_monitoring()
				self.assertIn("passwords", confirm.call_args.args[1])
				self.app.run_operation("status")
				self.assertIn("HTTP/SMTP tracing", confirm.call_args.args[1])
			self.assertFalse(self.app.monitor.active)
			self.app.backend_log.open_trace()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertIn("fixture-private-password", self.app.backend_log.text.get("1.0", "end"))
			self.assertNotIn("fixture-private-password", self.app.activity.get("1.0", "end"))
			self.app.backend_log.open()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertIn("fixture-native-log", self.app.backend_log.text.get("1.0", "end"))
			self.assertNotIn("fixture-private-password", self.app.backend_log.text.get("1.0", "end"))
			self.app.backend_log.close()
			self.app.search.set("--debug")
			row = self.app.reference.get_children()[0]
			self.assertEqual(self.app.reference.item(row, "values")[-1], "Available")
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			self.app.editor.options_values["debug_level"].set("3")
			self.assertTrue(self.app.editor.apply_options())
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.save()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertEqual(self.app.editor.document.config.getint("GUI", "DebugLevel"), 3)
			self.app.editor.document.config.set("GUI", "DebugLevel", "4")
			with patch("autoprimenet_gui.messagebox.askyesno") as confirm:
				self.app.start_monitoring()
				self.assertIn("debug verbosity", self.app.status.get())
				self.app.run_operation("status")
				self.assertIn("debug verbosity", self.app.status.get())
				confirm.assert_not_called()

	def test_native_lock_policy_controls_save_and_confirmation(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.search.set("--no-lock")
			row = self.app.reference.get_children()[0]
			self.assertEqual(self.app.reference.item(row, "values")[-1], "Available")
			self.app.reference.selection_set(row)
			self.app.open_reference_setting()
			self.app.editor.options_values["require_lock"].set("False")
			self.assertTrue(self.app.editor.apply_options())
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True) as confirm:
				self.app.save()
				self.assertIn("Native-lock success is not required", confirm.call_args.args[1])
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertFalse(self.app.editor.document.config.getboolean("PrimeNet", "require_lock"))
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=False) as confirm:
				self.app.start_monitoring()
				self.assertIn("independent CLI", confirm.call_args.args[1])
				self.app.run_operation("status")
				self.assertIn("atomic ownership guard", confirm.call_args.args[1])
			self.assertFalse(self.app.monitor.active)
			self.assertFalse((base / ".gui-runner.guard").exists())

	def test_tray_retry_filters_stale_events_and_restores_window(self):
		import subprocess
		from gui_controller import TrayController
		code = "import json,sys; print(json.dumps({'event':'ready'}),flush=True); sys.stdin.read()"
		def factory(_command, **kwargs):
			return subprocess.Popen([sys.executable, "-B", "-c", code], **kwargs)
		self.app.tray = TrayController(process_factory=factory)
		self.app.retry_tray()
		self.wait_until(lambda: self.app.tray.ready)
		first, generation = self.app.tray.process, self.app.tray.generation
		self.app.hide()
		self.assertTrue(self.app.hidden)
		first.terminate()
		self.wait_until(lambda: not self.app.hidden and not self.app.tray.ready)
		first.wait(timeout=5)
		self.app.retry_tray()
		self.wait_until(lambda: self.app.tray.ready)
		second = self.app.tray.process
		self.assertIsNot(first, second)
		self.app.retry_tray()
		self.assertIs(self.app.tray.process, second)
		for event in ("unavailable", "quit", "ready"):
			self.app.tray.events.put({"event": event, "generation": generation})
		delivered = []
		self.root.after(250, lambda: delivered.append(True))
		self.wait_until(lambda: bool(delivered))
		self.assertTrue(self.app.tray.ready)
		self.assertFalse(self.app.closed)
		self.assertIsNone(second.poll())

	def test_stalled_tray_startup_is_reaped_with_taskbar_fallback(self):
		import subprocess
		from gui_controller import TrayController
		def factory(_command, **kwargs):
			return subprocess.Popen([sys.executable, "-B", "-c", "import time; time.sleep(30)"], **kwargs)
		self.app.tray = TrayController(process_factory=factory)
		self.app.retry_tray()
		process = self.app.tray.process
		generation = self.app.tray.generation
		self.app.tray_deadline = time.monotonic() - 1
		self.wait_until(lambda: process.poll() is not None, timeout=7)
		self.assertGreater(self.app.tray.generation, generation)
		self.assertFalse(self.app.tray.ready)
		self.assertFalse(self.app.hidden)
		self.assertIn("taskbar", self.app.tray_status.get())

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
			self.assertEqual(set(editor.options_values), {"proxy_type", "ProxyHost", "ProxyUser", "encrypt", "require_lock"})
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

	def test_one_shot_actions_confirmation_no_overlap_and_unverified_completion(self):
		from gui_controller import MonitorController
		from gui_operations import OPERATIONS
		from test_gui_monitor import fake_monitor_process
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			text = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n[Email]\nfrom_email=sender@example.org\nsmtp_server=localhost\n"
			path.write_text(text)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.monitor = MonitorController(process_factory=fake_monitor_process)
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=False):
				self.app.run_operation("test_email")
			self.assertIsNone(self.app.monitor.process)
			self.assertFalse(list(Path(directory).glob("*.bak")))
			for key in ("ping", "test_email", "report_results", "upload_proofs"):
				with self.subTest(operation=key), patch("autoprimenet_gui.messagebox.askyesno", return_value=True) as confirm:
					self.app.run_operation(key)
					process = self.app.monitor.process
					self.app.run_operation(key)
					self.assertIs(self.app.monitor.process, process)
					confirm.assert_called_once()
					self.assertTrue(self.app.save_button.instate(["disabled"]))
					self.assertTrue(all(button.instate(["disabled"]) for button in self.app.operation_buttons.values()))
					self.wait_until(lambda: not self.app.monitor.active and self.app.monitor.state == "Stopped")
					self.assertIn(OPERATIONS[key].title, self.app.monitor_status.get())
					self.assertIn("unverified", self.app.monitor_status.get())
					self.assertEqual((Path(directory) / "operation.record").read_text(), key)
					self.assertEqual(path.read_text(), text)
			self.assertEqual((Path(directory) / "cycles.record").read_text().count("simulated"), 4)

	def test_one_shot_reference_navigation_does_not_run_and_dirty_form_blocks(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.search.set("--report-results")
			row = self.app.reference.get_children()[0]
			self.app.reference.selection_set(row)
			with patch("autoprimenet_gui.messagebox.askyesno") as confirm:
				self.app.open_reference_setting()
				self.assertEqual(self.app.notebook.select(), str(self.app.tabs["Assignments"]))
				self.assertIsNone(self.app.monitor.process)
				self.app.editor.values["ComputerID"].set("unsaved")
				self.app.run_operation("report_results")
				confirm.assert_not_called()
			self.assertIn("unsaved", self.app.status.get())

	def test_assignment_management_requires_typed_confirmation_and_snapshots(self):
		from gui_controller import MonitorController
		from test_gui_monitor import fake_monitor_process
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nComputerGUID=" + "a" * 32 + "\n")
			work = b"Test=127,70,1\n"
			(base / "worktodo.txt").write_bytes(work)
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.monitor = MonitorController(process_factory=fake_monitor_process)
			self.app.assignments.selection_set(self.app.assignments.get_children()[0])
			with patch("autoprimenet_gui.simpledialog.askinteger", return_value=127) as exponent, patch("autoprimenet_gui.simpledialog.askstring", return_value="wrong phrase"):
				self.app.run_operation("unreserve")
				self.assertEqual(exponent.call_args.kwargs["initialvalue"], 127)
			self.assertIsNone(self.app.monitor.process)
			self.assertFalse(list(base.glob(".gui-assignment-backup-*")))
			# Exercise and cancel the actual Tk confirmation, including its layout.
			dimensions = []
			def cancel_confirmation():
				for window in self.root.winfo_children():
					if hasattr(window, "cancel"):
						dimensions.append((window.winfo_reqwidth(), window.winfo_reqheight()))
						window.cancel()
			self.root.after(150, cancel_confirmation)
			self.app.run_operation("recover_all")
			self.assertEqual(len(dimensions), 1)
			self.assertLessEqual(dimensions[0][0], self.root.winfo_screenwidth())
			self.assertLessEqual(dimensions[0][1], self.root.winfo_screenheight())
			self.assertIsNone(self.app.monitor.process)
			with patch("autoprimenet_gui.simpledialog.askinteger", return_value=127), patch("autoprimenet_gui.simpledialog.askstring", return_value="UNRESERVE 127") as confirm:
				self.app.run_operation("unreserve")
				self.assertIn("FIRST matching exponent", confirm.call_args.args[1].replace("\n", " "))
				self.wait_until(lambda: not self.app.monitor.active and self.app.monitor.state == "Stopped")
			self.assertEqual((base / "worktodo.txt").read_bytes(), work)
			folders = list(base.glob(".gui-assignment-backup-*"))
			self.assertEqual(len(folders), 1)
			self.assertEqual((folders[0] / "worker-1-work.bin").read_bytes(), work)
			self.assertIn("Private work/certification snapshot", self.app.activity.get("1.0", "end"))
			with patch("autoprimenet_gui.simpledialog.askstring", return_value="RECOVER ALL"):
				self.app.run_operation("recover_all")
				self.wait_until(lambda: not self.app.monitor.active and self.app.monitor.state == "Stopped")
			self.assertEqual(len(list(base.glob(".gui-assignment-backup-*"))), 2)
			self.assertEqual((base / "operation.record").read_text(), "recover_all")

	def test_registration_batch_offline_preview_edit_and_simulated_registration(self):
		from gui_controller import MonitorController
		from test_gui_monitor import fake_monitor_process
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nComputerGUID=" + "a" * 32 + "\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.monitor = MonitorController(process_factory=fake_monitor_process)
			self.app.run_operation("register_exponents")
			form = self.app.registration
			self.assertTrue(form.window.winfo_exists())
			self.root.update()
			self.assertLessEqual(form.launch_button.winfo_rooty() + form.launch_button.winfo_height(), form.window.winfo_rooty() + form.window.winfo_height())
			form.values["exponent"].set("127")
			self.assertTrue(form.add())
			form.values["exponent"].set("131")
			self.assertTrue(form.add())
			form.request_preview()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertIsNotNone(form.preview)
			self.assertIn("PRP=1,2,127", form.output.get("1.0", "end"))
			self.assertFalse((base / "worktodo.txt").exists())
			form.table.selection_set(form.table.get_children()[0])
			self.root.update()
			form.values["exponent"].set("137")
			self.assertTrue(form.replace())
			self.assertIsNone(form.preview)
			self.assertTrue(form.launch_button.instate(["disabled"]))
			form.request_preview()
			self.wait_until(lambda: not self.app.jobs.busy)
			with patch("autoprimenet_gui.simpledialog.askstring", return_value="wrong"):
				form.launch()
			self.assertIsNone(self.app.monitor.process)
			with patch("autoprimenet_gui.simpledialog.askstring", return_value="REGISTER 2"):
				form.launch()
			self.assertIsNone(form.window)
			self.wait_until(lambda: not self.app.monitor.active and self.app.monitor.state == "Stopped")
			self.assertEqual((base / "operation.record").read_text(), "register_exponents")
			self.assertTrue(list(base.glob(".gui-assignment-backup-*")))
			self.assertFalse((base / "worktodo.txt").exists())

	def test_registration_batch_discard_guards_and_closed_preview_result(self):
		with tempfile.TemporaryDirectory() as directory:
			(Path(directory) / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.run_operation("register_exponents")
			form = self.app.registration
			form.values["exponent"].set("127")
			form.add()
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=False):
				self.app.refresh()
				self.app.quit()
			self.assertFalse(self.app.closed)
			self.assertTrue(form.dirty)
			form.request_preview()
			form.close()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertIsNone(form.window)
			self.assertFalse((Path(directory) / "worktodo.txt").exists())

	def test_native_log_private_diagnostics_and_original_help(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
			(base / "autoprimenet.log").write_text("PRIVATE-NATIVE-TEST-CONTENT\n")
			self.app.directory.set(directory)
			self.app.refresh()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.app.backend_log.open()
			self.wait_until(lambda: not self.app.jobs.busy)
			self.assertIn("PRIVATE-NATIVE-TEST-CONTENT", self.app.backend_log.text.get("1.0", "end"))
			self.assertNotIn("PRIVATE-NATIVE-TEST-CONTENT", self.app.activity.get("1.0", "end"))
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=False):
				self.app.request_diagnostics()
			self.assertFalse(list(base.glob(".gui-debug-report-*")))
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.request_diagnostics()
				self.wait_until(lambda: not self.app.jobs.busy)
			self.assertEqual(len(list(base.glob(".gui-debug-report-*"))), 1)
			self.assertIn("Private diagnostics saved", self.app.status.get())
			with patch.object(self.app, "show_text_report") as report:
				self.app.request_cli_help()
				self.wait_until(lambda: not self.app.jobs.busy)
				report.assert_called_once()
				self.assertIn("usage: autoprimenet.py", report.call_args.args[1])
				self.assertIn("--register-exponents", report.call_args.args[1])
			with patch("autoprimenet_gui.messagebox.showinfo") as about:
				self.app.show_about()
				self.assertIn("2.0.2", about.call_args.args[1])
			self.app.backend_log.close()

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
			if sys.platform in {"darwin", "win32"} and native_tray_installed():
				self.app.tray.start()
				self.wait_until(lambda: self.app.tray.ready)
			with patch("autoprimenet_gui.messagebox.askyesno", return_value=True):
				self.app.start_monitoring()
			self.wait_until(lambda: self.app.monitor.state in {"Waiting", "Watching files"})
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

	@unittest.skipUnless(sys.platform in {"darwin", "win32"}, "Native macOS/Windows tray test")
	def test_quit_stops_healthy_tray_helper(self):
		if not native_tray_installed():
			self.skipTest("Install requirements-gui-tray.txt for native tray checks")
		self.app.tray.start()
		self.wait_until(lambda: self.app.tray.ready)
		process = self.app.tray.process
		self.app.quit()
		self.assertEqual(process.wait(timeout=6), 0)

	@unittest.skipUnless(sys.platform in {"darwin", "win32"}, "Native macOS/Windows tray test")
	def test_tray_hide_restore_helper_failure_and_clean_shutdown(self):
		if not native_tray_installed():
			self.skipTest("Install requirements-gui-tray.txt for native tray checks")
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
