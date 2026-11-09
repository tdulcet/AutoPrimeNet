"""Bounded private backend-log reading and offline diagnostic export.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import os
from pathlib import Path
import stat
import tempfile
import tkinter as tk
from tkinter import ttk

from gui_config import ConfigDocument, WorkspaceError
from gui_controller import backend_request


MAX_LOG_BYTES = 128 * 1024


def read_backend_tail(document):
	name = document.config.get("PrimeNet", "logfile", fallback="autoprimenet.log")
	path = document.directory / name
	return _read_tail(path)


def read_latest_trace(document):
	candidates = []
	for path in document.directory.glob(".gui-backend-trace-*.log"):
		try:
			info = path.lstat()
		except FileNotFoundError:
			continue
		if stat.S_ISREG(info.st_mode):
			candidates.append((info.st_mtime_ns, path.name, path))
	if not candidates:
		raise WorkspaceError("No private backend trace is available in this workspace.")
	return _read_tail(max(candidates)[2])


def _read_tail(path):
	try:
		before = path.lstat()
		if not stat.S_ISREG(before.st_mode):
			raise WorkspaceError("The backend log must be a regular, non-symlink file.")
		with os.fdopen(os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)), "rb") as stream:
			info = os.fstat(stream.fileno())
			if not stat.S_ISREG(info.st_mode) or (info.st_dev, info.st_ino) != (before.st_dev, before.st_ino):
				raise WorkspaceError("The backend log rotated during opening; refresh again.")
			offset = max(0, info.st_size - MAX_LOG_BYTES)
			stream.seek(offset)
			data = stream.read(MAX_LOG_BYTES)
	except OSError as error:
		raise WorkspaceError("The configured backend log is unavailable or cannot be read.") from error
	if offset and b"\n" in data:
		data = data.split(b"\n", 1)[1]
	lines = data.decode("utf-8", errors="replace").replace("\x00", "�").splitlines()
	return {"path": str(path), "text": "\n".join(lines[-2000:]), "truncated": bool(offset or len(lines) > 2000)}


def export_debug_report(document):
	if ConfigDocument(str(document.directory), document.path.name).version != document.version:
		raise WorkspaceError("Configuration changed; refresh before exporting diagnostics.")
	result = backend_request("debug_report", text=document.text, directory=str(document.directory), config_name=document.path.name)
	text = result["text"]
	if not isinstance(text, str) or len(text.encode("utf-8")) > 256 * 1024:
		raise WorkspaceError("The diagnostic report is invalid or too large.")
	if ConfigDocument(str(document.directory), document.path.name).version != document.version:
		raise WorkspaceError("Configuration changed during diagnostics; refresh and retry.")
	path = None
	try:
		with tempfile.NamedTemporaryFile("w", prefix=".gui-debug-report-", suffix=".txt", dir=document.directory, encoding="utf-8", delete=False) as stream:
			path = Path(stream.name)
			stream.write("PRIVATE diagnostic report — generated offline; review before sharing.\n\n" + text)
			stream.flush()
			os.fsync(stream.fileno())
		return {"path": str(path)}
	except BaseException:
		if path is not None:
			path.unlink(missing_ok=True)
		raise


class BackendLogWindow:
	def __init__(self, app):
		self.app = app
		self.window = None

	def open(self):
		return self._open(False)

	def open_trace(self):
		return self._open(True)

	def _open(self, trace):
		if self.app.jobs.busy or self.app.editor.document is None:
			return
		if self.window is not None and self.window.winfo_exists():
			if self.trace_mode == trace:
				self.window.lift()
				self.refresh()
				return
			self.close()
		self.trace_mode = trace
		self.document = self.app.editor.document
		self.window = window = tk.Toplevel(self.app.root)
		window.title("Latest private AutoPrimeNet trace" if trace else "Private AutoPrimeNet backend log")
		window.geometry("900x560")
		outer = ttk.Frame(window, padding=12)
		outer.pack(fill="both", expand=True)
		intro = "Private raw trace: may contain passwords, tokens and message bodies. Review/redact before sharing. Latest file only." if trace else "Private native log: may contain account details, paths or verbose diagnostics. Review/redact before sharing."
		ttk.Label(outer, text=intro + "\nThis bounded snapshot is not copied into GUI activity. Refresh to read new output.", wraplength=850).pack(anchor="w")
		self.path_label = tk.StringVar(value="Reading configured log…")
		ttk.Label(outer, textvariable=self.path_label, wraplength=850).pack(anchor="w", pady=6)
		frame = ttk.Frame(outer)
		frame.pack(fill="both", expand=True)
		self.text = tk.Text(frame, wrap="word", state="disabled")
		scrollbar = ttk.Scrollbar(frame, orient="vertical", command=self.text.yview)
		self.text.configure(yscrollcommand=scrollbar.set)
		scrollbar.pack(side="right", fill="y")
		self.text.pack(side="left", fill="both", expand=True)
		self.refresh_button = ttk.Button(outer, text="Refresh latest trace" if trace else "Refresh backend log", command=self.refresh)
		self.refresh_button.pack(anchor="w", pady=(8, 0))
		window.protocol("WM_DELETE_WINDOW", self.close)
		self.refresh()
		return window

	def refresh(self):
		if not self.app.jobs.busy and self.app.jobs.submit("backend_log", read_latest_trace if self.trace_mode else read_backend_tail, self.document):
			self.app.set_busy(True)

	def set_busy(self, busy):
		if self.window is not None and self.window.winfo_exists():
			self.refresh_button.state(["disabled"] if busy else ["!disabled"])

	def complete(self, value, error):
		if self.window is None or not self.window.winfo_exists():
			return
		if error:
			self.path_label.set(str(error) if isinstance(error, WorkspaceError) else "Backend log preview failed.")
			return
		self.path_label.set(value["path"] + (" — latest 128 KiB / 2000 lines only" if value["truncated"] else ""))
		self.text.configure(state="normal")
		self.text.delete("1.0", "end")
		self.text.insert("end", value["text"])
		self.text.configure(state="disabled")
		self.text.see("end")

	def close(self):
		if self.window is not None and self.window.winfo_exists():
			self.window.destroy()
		self.window = None
