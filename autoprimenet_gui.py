#!/usr/bin/env python3
"""Optional Tkinter GUI foundation for AutoPrimeNet (offline preview).

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import sys

if sys.version_info < (3, 15):
	print("AutoPrimeNet GUI requires Python 3.15.0 or later.", file=sys.stderr)
	sys.exit(2)

import argparse
import queue
import time

try:
	import tkinter as tk
	from tkinter import filedialog, messagebox, ttk
except ImportError:
	print("Tkinter is unavailable. Install the Tk bindings matching this Python; see GUI.md.", file=sys.stderr)
	sys.exit(2)

from gui_config import WorkspaceError, inspect_workspace
from gui_controller import BackgroundJobs, ControllerError, TrayController, backend_request


TABS = ("Dashboard", "Assignments", "Workers", "PrimeNet", "Advanced", "Notifications", "Logs & Status", "Settings")
WORK_TYPES = {2: "TF", 3: "P-1", 4: "P-1", 5: "ECM", 6: "P+1", 100: "LL", 101: "LL double-check", 150: "PRP", 200: "Certification"}


class Application:
	def __init__(self, root, tray=True):
		self.root = root
		self.jobs = BackgroundJobs()
		self.tray = TrayController()
		self.hidden = False
		self.closed = False
		self.options = []
		self.tray_deadline = time.monotonic() + 15
		self.directory = tk.StringVar()
		self.config_name = tk.StringVar(value="prime.ini")
		self.status = tk.StringVar(value="Offline preview — no monitoring or server operations")
		self.summary = tk.StringVar(value="Choose a working directory to inspect local configuration and assignments.")
		self.tray_status = tk.StringVar(value="Starting tray helper…" if tray else "Tray disabled; close minimizes the window.")
		self.search = tk.StringVar()
		root.title("AutoPrimeNet GUI — Offline Preview")
		root.geometry("1050x700")
		root.minsize(780, 520)
		root.protocol("WM_DELETE_WINDOW", self.hide)
		if sys.platform == "darwin":
			root.createcommand("tk::mac::Quit", self.quit)
		self._build()
		if tray:
			self.tray.start()
		self.jobs.submit("capabilities", backend_request, "capabilities")
		self.root.after(100, self.poll)

	def _build(self):
		menu = tk.Menu(self.root)
		file_menu = tk.Menu(menu, tearoff=False)
		file_menu.add_command(label="Choose working directory…", command=self.choose_directory)
		file_menu.add_command(label="Reload local preview", command=self.refresh)
		file_menu.add_separator()
		file_menu.add_command(label="Hide to tray / minimize", command=self.hide)
		file_menu.add_command(label="Quit", command=self.quit)
		menu.add_cascade(label="File", menu=file_menu)
		view = tk.Menu(menu, tearoff=False)
		for name in TABS:
			view.add_command(label=name, command=lambda selected=name: self.notebook.select(self.tabs[selected]))
		menu.add_cascade(label="View", menu=view)
		help_menu = tk.Menu(menu, tearoff=False)
		help_menu.add_command(label="CLI reference", command=lambda: self.notebook.select(self.tabs["Advanced"]))
		help_menu.add_command(label="About", command=lambda: messagebox.showinfo(
			"About AutoPrimeNet GUI", "Optional GUI foundation\nPython 3.15.0 or later\nGPL-3.0\n\nOffline preview only; no server operations or monitoring yet.", parent=self.root))
		menu.add_cascade(label="Help", menu=help_menu)
		self.root.config(menu=menu)
		bar = ttk.Frame(self.root, padding=10)
		bar.pack(fill="x")
		ttk.Label(bar, text="Working directory").pack(side="left")
		ttk.Entry(bar, textvariable=self.directory).pack(side="left", fill="x", expand=True, padx=8)
		ttk.Button(bar, text="Browse…", command=self.choose_directory).pack(side="left")
		self.reload_button = ttk.Button(bar, text="Refresh preview", command=self.refresh)
		self.reload_button.pack(side="left", padx=(8, 0))
		self.notebook = ttk.Notebook(self.root)
		self.notebook.pack(fill="both", expand=True, padx=10, pady=(0, 8))
		self.tabs = {}
		for name in TABS:
			frame = ttk.Frame(self.notebook, padding=14)
			self.notebook.add(frame, text=name)
			self.tabs[name] = frame
		ttk.Label(self.tabs["Dashboard"], text="Local workspace", font=("TkDefaultFont", 16)).pack(anchor="w")
		ttk.Label(self.tabs["Dashboard"], textvariable=self.summary, justify="left", wraplength=720).pack(anchor="w", pady=12)
		ttk.Label(self.tabs["Dashboard"], text="PrimeNet: not checked\nMonitoring: not implemented\nProgress and completion estimates: unavailable", justify="left").pack(anchor="w")
		ttk.Label(self.tabs["Dashboard"], textvariable=self.tray_status, wraplength=720).pack(anchor="w", pady=16)
		self.assignments = self._table(self.tabs["Assignments"], ("Worker", "Exponent", "Work type", "Local AID", "Server confirmation"))
		ttk.Label(self.tabs["Assignments"], text="Read-only preview. Parsed work lines and local AIDs do not confirm current server reservations.", wraplength=720).pack(anchor="w", pady=8)
		self.workers = self._table(self.tabs["Workers"], ("Worker", "Directory", "Preference", "Work file"))
		for name, explanation in (
			("PrimeNet", "Account editing, registration, scheduling and network diagnostics are not available in this milestone."),
			("Notifications", "Notification settings and test messages are not available in this milestone. No messages are sent."),
		):
			ttk.Label(self.tabs[name], text=explanation, wraplength=720, justify="left").pack(anchor="w")
		ttk.Label(self.tabs["Advanced"], text="Search the existing CLI options (reference only; graphical controls are still being implemented).").pack(anchor="w")
		entry = ttk.Entry(self.tabs["Advanced"], textvariable=self.search)
		entry.pack(fill="x", pady=8)
		self.search.trace_add("write", lambda *_: self.filter_options())
		self.reference = self._table(self.tabs["Advanced"], ("CLI flags", "Destination"))
		self.activity = tk.Text(self.tabs["Logs & Status"], wrap="word", state="disabled", height=12)
		self.activity.pack(fill="both", expand=True)
		ttk.Label(self.tabs["Logs & Status"], text="GUI activity only. Existing logs and credentials are not loaded.").pack(anchor="w", pady=8)
		ttk.Label(self.tabs["Settings"], text="Configuration filename (read only; no changes are saved)").pack(anchor="w")
		ttk.Entry(self.tabs["Settings"], textvariable=self.config_name, width=40).pack(anchor="w", pady=8)
		ttk.Label(self.tabs["Settings"], text="Closing hides to the tray/menu bar when ready; otherwise it minimizes.\nUse File → Quit to exit.\nSee GUI.md and GUI_DEVELOPMENT.md for requirements and current limitations.", justify="left", wraplength=720).pack(anchor="w", pady=12)
		ttk.Label(self.root, textvariable=self.status, relief="sunken", anchor="w", padding=5).pack(fill="x", side="bottom")

	def _table(self, parent, columns):
		frame = ttk.Frame(parent)
		frame.pack(fill="both", expand=True)
		table = ttk.Treeview(frame, columns=columns, show="headings")
		for name in columns:
			table.heading(name, text=name)
			table.column(name, width=150, minwidth=70)
		scroll = ttk.Scrollbar(frame, orient="vertical", command=table.yview)
		horizontal = ttk.Scrollbar(frame, orient="horizontal", command=table.xview)
		table.configure(yscrollcommand=scroll.set, xscrollcommand=horizontal.set)
		table.grid(row=0, column=0, sticky="nsew")
		scroll.grid(row=0, column=1, sticky="ns")
		horizontal.grid(row=1, column=0, sticky="ew")
		frame.rowconfigure(0, weight=1)
		frame.columnconfigure(0, weight=1)
		return table

	def log(self, text):
		self.activity.config(state="normal")
		self.activity.insert("end", time.strftime("%H:%M:%S ") + text + "\n")
		self.activity.see("end")
		self.activity.config(state="disabled")

	def choose_directory(self):
		directory = filedialog.askdirectory(parent=self.root, title="Choose AutoPrimeNet working directory")
		if directory:
			self.directory.set(directory)
			self.refresh()

	def refresh(self):
		if not self.directory.get().strip():
			return
		if self.jobs.submit("workspace", inspect_workspace, self.directory.get(), self.config_name.get()):
			self.status.set("Reading local workspace…")
			self.reload_button.state(["disabled"])

	def display_workspace(self, snapshot):
		identity = snapshot["identity"]
		self.summary.set("Username: {}\nComputer: {}\nProgram: {}\nConfiguration: {}\nWorkers: {}\nFree disk space: {:.1f} GiB\nNew-work requests: {} (configured state)".format(
			identity["username"], identity["computer"], snapshot["engine"],
			"Found" if snapshot["config_present"] else "Not found; showing defaults",
			len(snapshot["workers"]), snapshot["free_bytes"] / 1024**3,
			"disabled" if snapshot["new_work_disabled"] else "not disabled",
		))
		for table in (self.workers, self.assignments):
			table.delete(*table.get_children())
		for worker in snapshot["workers"]:
			self.workers.insert("", "end", values=(worker["number"], worker["directory"], worker["preference"], worker["work_file"]))
		for item in snapshot["assignments"]:
			if item["parsed"]:
				fields = item["fields"]
				work_type = "PRP double-check" if fields["prp_dblchk"] else WORK_TYPES.get(fields["work_type"], "Unknown")
				self.assignments.insert("", "end", values=(item["worker"], fields["n"], work_type, fields["uid"] or "None", "Unverified"))
			else:
				self.assignments.insert("", "end", values=(item["worker"], "—", "Unrecognized line", "—", "Unavailable"))
		self.status.set("Local preview refreshed — no files changed or server contacted")
		self.log("Local workspace preview refreshed.")

	def filter_options(self):
		self.reference.delete(*self.reference.get_children())
		term = self.search.get().casefold()
		for option in self.options:
			flags = ", ".join(option["flags"])
			if term in (flags + " " + option["dest"]).casefold():
				self.reference.insert("", "end", values=(flags, option["dest"]))

	def poll(self):
		if self.closed:
			return
		result = self.jobs.take()
		if result:
			name, value, error = result
			self.reload_button.state(["!disabled"])
			if error:
				# ConfigParser and OS exceptions can contain raw file contents or
				# private paths. Keep the visible failure generic for this preview.
				self.status.set(str(error) if isinstance(error, (WorkspaceError, ControllerError)) else "Preview failed; check the directory, configuration and Python environment.")
				self.log("Preview failed. No changes were made.")
			elif name == "capabilities":
				self.options = value["cli_options"]
				self.filter_options()
				self.log("Offline backend ready; CLI reference loaded.")
			elif name == "workspace":
				self.display_workspace(value)
		while True:
			try:
				event = self.tray.events.get_nowait()
			except queue.Empty:
				break
			if event == "ready":
				self.tray.ready = True
				self.tray_status.set("Tray/menu bar ready. Close hides the window; use its menu to reopen.")
			elif event == "open":
				self.show()
			elif event == "quit":
				self.quit()
			else:
				self.tray.ready = False
				self.tray_status.set("Tray unavailable. Close minimizes to the taskbar/Dock.")
				if self.hidden:
					self.show()
		if not self.tray.ready and time.monotonic() > self.tray_deadline:
			self.tray_status.set("Tray unavailable. Close minimizes to the taskbar/Dock.")
		if not self.closed:
			self.root.after(100, self.poll)

	def hide(self):
		if self.tray.ready and self.tray.process is not None and self.tray.process.poll() is None:
			self.hidden = True
			self.root.withdraw()
		else:
			self.root.iconify()

	def show(self):
		self.hidden = False
		self.root.deiconify()
		self.root.lift()

	def quit(self):
		# No monitoring child exists in this milestone. Wait for a bounded local
		# read to finish rather than orphaning its private bridge on GUI exit.
		if self.jobs.busy:
			self.show()
			self.status.set("A local preview is still running; quit when it completes.")
			return
		self.closed = True
		self.tray.stop()
		self.jobs.close()
		self.root.destroy()


def main():
	parser = argparse.ArgumentParser(description=__doc__)
	parser.add_argument("--no-tray", action="store_true", help="Minimize to the taskbar/Dock instead of using a tray helper")
	args = parser.parse_args()
	root = tk.Tk()
	Application(root, tray=not args.no_tray)
	root.mainloop()


if __name__ == "__main__":
	main()
