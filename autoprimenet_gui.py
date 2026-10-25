#!/usr/bin/env python3
"""Optional Tkinter configuration and scheduled monitoring for AutoPrimeNet.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import sys

if sys.version_info < (3, 15):
	print("AutoPrimeNet GUI requires Python 3.15.0 or later.", file=sys.stderr)
	sys.exit(2)

import argparse
from pathlib import Path
import queue
import time

try:
	import tkinter as tk
	from tkinter import filedialog, messagebox, ttk
except ImportError:
	print("Tkinter is unavailable. Install the Tk bindings matching this Python; see GUI.md.", file=sys.stderr)
	sys.exit(2)

from gui_config import WorkspaceError, load_editor_workspace, save_configuration
from gui_controller import BackgroundJobs, ControllerError, MonitorController, TrayController, backend_request
from gui_forms import ConfigurationForms
from gui_options import field_for_destination


TABS = ("Dashboard", "Assignments", "Workers", "PrimeNet", "Advanced", "Notifications", "Logs & Status", "Settings")
WORK_TYPES = {2: "TF", 3: "P-1", 4: "P-1", 5: "ECM", 6: "P+1", 100: "LL", 101: "LL double-check", 150: "PRP", 200: "Certification"}


class Application:
	def __init__(self, root, tray=True):
		self.root = root
		self.jobs = BackgroundJobs()
		self.tray = TrayController()
		self.monitor = MonitorController()
		self.quit_pending = False
		self.hidden = False
		self.closed = False
		self.options = []
		self.tray_deadline = time.monotonic() + 15
		self.directory = tk.StringVar()
		self.config_name = tk.StringVar(value="prime.ini")
		self.status = tk.StringVar(value="Monitoring stopped — local previews and configuration")
		self.monitor_status = tk.StringVar(value="Scheduled monitoring: Stopped\nPrimeNet connectivity: not checked")
		self.summary = tk.StringVar(value="Choose a working directory to inspect local configuration and assignments.")
		self.tray_status = tk.StringVar(value="Starting tray helper…" if tray else "Tray disabled; close minimizes the window.")
		self.search = tk.StringVar()
		root.title("AutoPrimeNet GUI")
		root.geometry("1050x700")
		root.minsize(780, 520)
		root.protocol("WM_DELETE_WINDOW", self.hide)
		if sys.platform == "darwin":
			root.createcommand("tk::mac::Quit", self.quit)
		self._build()
		self.set_busy(False)
		if tray:
			self.tray.start()
		self.jobs.submit("capabilities", backend_request, "capabilities")
		self.root.after(100, self.poll)

	def _build(self):
		menu = tk.Menu(self.root)
		file_menu = tk.Menu(menu, tearoff=False)
		file_menu.add_command(label="Choose working directory…", command=self.choose_directory)
		file_menu.add_command(label="Reload local preview", command=self.refresh)
		file_menu.add_command(label="Save local configuration", command=self.save)
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
			"About AutoPrimeNet GUI", "Optional GUI foundation\nPython 3.15.0 or later\nGPL-3.0\n\nLocal configuration and scheduled CLI monitoring. Immediate file watching and full graphical parity are not available yet.", parent=self.root))
		menu.add_cascade(label="Help", menu=help_menu)
		self.root.config(menu=menu)
		bar = ttk.Frame(self.root, padding=10)
		bar.pack(fill="x")
		ttk.Label(bar, text="Working directory").pack(side="left")
		self.directory_entry = ttk.Entry(bar, textvariable=self.directory)
		self.directory_entry.pack(side="left", fill="x", expand=True, padx=8)
		self.browse_button = ttk.Button(bar, text="Browse…", command=self.choose_directory)
		self.browse_button.pack(side="left")
		self.reload_button = ttk.Button(bar, text="Refresh preview", command=self.refresh)
		self.reload_button.pack(side="left", padx=(8, 0))
		self.save_button = ttk.Button(bar, text="Save settings", command=self.save, state="disabled")
		self.save_button.pack(side="left", padx=(8, 0))
		self.notebook = ttk.Notebook(self.root)
		self.notebook.pack(fill="both", expand=True, padx=10, pady=(0, 8))
		self.tabs = {}
		for name in TABS:
			frame = ttk.Frame(self.notebook, padding=14)
			self.notebook.add(frame, text=name)
			self.tabs[name] = frame
		self.editor = ConfigurationForms(self)
		ttk.Label(self.tabs["Dashboard"], text="Local workspace", font=("TkDefaultFont", 16)).pack(anchor="w")
		ttk.Label(self.tabs["Dashboard"], textvariable=self.summary, justify="left", wraplength=720).pack(anchor="w", pady=12)
		ttk.Label(self.tabs["Dashboard"], textvariable=self.monitor_status, justify="left").pack(anchor="w")
		controls = ttk.Frame(self.tabs["Dashboard"])
		controls.pack(anchor="w", pady=8)
		self.start_button = ttk.Button(controls, text="Start scheduled monitoring…", command=self.start_monitoring)
		self.start_button.pack(side="left")
		self.stop_button = ttk.Button(controls, text="Stop after current cycle", command=self.stop_monitoring)
		self.stop_button.pack(side="left", padx=8)
		self.force_button = ttk.Button(controls, text="Force stop…", command=self.force_stop_monitoring)
		self.force_button.pack(side="left")
		ttk.Label(self.tabs["Dashboard"], textvariable=self.tray_status, wraplength=720).pack(anchor="w", pady=16)
		self.assignments = self._table(self.tabs["Assignments"], ("Worker", "Exponent", "Work type", "Local AID", "Server confirmation"))
		ttk.Label(self.tabs["Assignments"], text="Read-only preview. Parsed work lines and local AIDs do not confirm current server reservations.", wraplength=720).pack(anchor="w", pady=8)
		self.workers = self._table(self.tabs["Workers"], ("Worker", "Directory", "Preference", "Work file"))
		for name, explanation in (
			("PrimeNet", "Save changes locally with Save settings. Start scheduled monitoring from Dashboard when ready to communicate with PrimeNet. Standalone registration and diagnostics remain unfinished."),
			("Notifications", "Save notification settings locally with Save settings. Blank boolean values use the backend default. Scheduled monitoring can send configured messages. Manage passwords to replace or remove SMTP/proxy passwords; replacements require encryption. Test-message sending is not yet available. Set Send configured notifications to False to suppress sending."),
		):
			ttk.Label(self.tabs[name], text=explanation, wraplength=720, justify="left").pack(anchor="w")
		ttk.Label(self.tabs["Advanced"], text="Search the existing CLI options (reference only; graphical controls are still being implemented).").pack(anchor="w")
		entry = ttk.Entry(self.tabs["Advanced"], textvariable=self.search)
		entry.pack(fill="x", pady=8)
		self.search.trace_add("write", lambda *_: self.filter_options())
		self.reference = self._table(self.tabs["Advanced"], ("CLI flags", "Destination", "GUI location"))
		self.reference.bind("<Double-1>", self.open_reference_setting)
		self.reference.bind("<Return>", self.open_reference_setting)
		self.activity = tk.Text(self.tabs["Logs & Status"], wrap="word", state="disabled", height=12)
		self.activity.pack(fill="both", expand=True)
		ttk.Label(self.tabs["Logs & Status"], text="GUI activity only. Existing logs and credentials are not loaded.").pack(anchor="w", pady=8)
		ttk.Label(self.tabs["Settings"], text="Configuration filename (reload after changing)").pack(anchor="w")
		self.config_entry = ttk.Entry(self.tabs["Settings"], textvariable=self.config_name, width=40)
		self.config_entry.pack(anchor="w", pady=8)
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
		lines = int(self.activity.index("end-1c").split(".")[0])
		if lines > 2000:
			self.activity.delete("1.0", "{}.0".format(lines - 2000 + 1))
		self.activity.see("end")
		self.activity.config(state="disabled")

	def choose_directory(self):
		if self.jobs.busy or self.monitor.active or not self.discard_changes():
			return
		directory = filedialog.askdirectory(parent=self.root, title="Choose AutoPrimeNet working directory")
		if directory:
			self.editor.dirty = False
			self.directory.set(directory)
			self.refresh()

	def discard_changes(self):
		return not self.editor.dirty or messagebox.askyesno("Unsaved configuration", "Discard the unsaved form changes?", parent=self.root)

	def set_busy(self, busy):
		active = self.monitor.active
		self.reload_button.state(["disabled"] if busy or self.quit_pending else ["!disabled"])
		for widget in (self.browse_button, self.directory_entry, self.config_entry):
			widget.state(["disabled"] if busy or active or self.quit_pending else ["!disabled"])
		self.editor.set_enabled(not busy and not active and not self.quit_pending and self.editor.document is not None)
		self.save_button.state(["disabled"] if busy or active or self.quit_pending or self.editor.document is None else ["!disabled"])
		self.start_button.state(["disabled"] if busy or active or self.quit_pending or self.editor.document is None else ["!disabled"])
		self.stop_button.state(["!disabled"] if active and self.monitor.state != "Stopping" else ["disabled"])
		self.force_button.state(["!disabled"] if active else ["disabled"])

	def refresh(self):
		if self.jobs.busy or self.quit_pending or not self.directory.get().strip() or not self.discard_changes():
			return
		if self.jobs.submit("workspace", load_editor_workspace, self.directory.get(), self.config_name.get()):
			self.status.set("Reading local workspace…")
			self.set_busy(True)

	def save(self):
		if self.jobs.busy or self.monitor.active or self.quit_pending or self.editor.document is None:
			return
		document = self.editor.document
		if Path(self.directory.get()).expanduser().resolve() != document.directory or self.config_name.get() != document.path.name:
			self.status.set("Reload the selected directory/configuration filename before saving.")
			return
		try:
			values, engine, workers, credentials = self.editor.collect()
		except ValueError as error:
			self.status.set(str(error))
			return
		if not messagebox.askyesno("Save local configuration", "Validate and save the displayed settings locally? An existing configuration will be backed up. No server will be contacted. Stop any independently running AutoPrimeNet before saving.", parent=self.root):
			return
		if self.jobs.submit("save", save_configuration, document, values, engine, workers, credentials):
			self.status.set("Validating and saving local configuration…")
			self.set_busy(True)

	def start_monitoring(self):
		self.show()
		if self.jobs.busy or self.monitor.active or self.quit_pending or self.editor.document is None:
			return
		if self.editor.dirty:
			self.status.set("Save or reload unsaved changes before starting monitoring.")
			return
		document = self.editor.document
		if Path(self.directory.get()).expanduser().resolve() != document.directory or self.config_name.get() != document.path.name:
			self.status.set("Reload the selected workspace before starting monitoring.")
			return
		if document.version is None:
			self.status.set("Save the configuration before starting monitoring.")
			return
		try:
			hours = document.config.getint("PrimeNet", "HoursBetweenCheckins", fallback=1)
			if not 1 <= hours <= 168:
				raise ValueError
		except ValueError:
			self.status.set("Correct and save the progress check-in interval before starting monitoring.")
			return
		if not messagebox.askyesno("Start scheduled monitoring", "Run AutoPrimeNet in this workspace now, then every {} hour(s)?\n\nCycles can register/update this computer, request/register assignments, report results/progress, download certification data, upload proofs and send configured notifications. Successfully uploaded proofs are archived or deleted according to the existing configuration.\n\nThis mode checks at the scheduled interval; it does not watch files immediately. Stop waits for the current cycle to finish. Computation engines are never started or stopped.".format(hours), parent=self.root):
			return
		try:
			self.monitor.start(document)
		except ControllerError as error:
			self.status.set(str(error))
			return
		self.update_monitor_state("Starting")

	def update_monitor_state(self, state, detail=""):
		self.monitor.state = state
		self.status.set("Scheduled monitoring: " + state)
		self.monitor_status.set("Scheduled monitoring: " + state + ("\n" + detail if detail else "") + "\nServer acceptance/connectivity: unverified")
		self.tray.set_state(state)
		self.set_busy(self.jobs.busy)

	def stop_monitoring(self):
		if self.monitor.active:
			self.monitor.stop()
			self.update_monitor_state("Stopping", "Waiting for the current CLI cycle to finish safely.")

	def force_stop_monitoring(self):
		if self.monitor.active and messagebox.askyesno("Force stop monitoring", "Terminate only the CLI process launched by this GUI? This can interrupt a write or upload and leave sidecar locks behind. They will not be deleted automatically. Computation engines are not affected.", parent=self.root):
			self.monitor.stop(force=True)
			self.update_monitor_state("Stopping", "Forced shutdown requested; runtime files may need inspection.")

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
		self.status.set("Local preview refreshed; monitoring continues separately." if self.monitor.active else "Local preview refreshed — no files changed or server contacted")
		self.log("Local workspace preview refreshed.")

	def filter_options(self):
		self.reference.delete(*self.reference.get_children())
		term = self.search.get().casefold()
		for option in self.options:
			flags = ", ".join(option["flags"])
			field = field_for_destination(option["dest"])
			location = field.tab + " → " + (field.dialog + " → " if field.dialog else "") + field.label if field else "Not mapped in this reference"
			if option["dest"] in {"email_password", "proxy_password"}:
				location = "Notifications → Manage passwords" if option["dest"] == "email_password" else "Settings → Manage passwords"
			if term in (flags + " " + option["dest"] + " " + location).casefold():
				self.reference.insert("", "end", values=(flags, option["dest"], location))

	def open_reference_setting(self, _event=None):
		selected = self.reference.selection()
		if not selected:
			return
		destination = self.reference.item(selected[0], "values")[1]
		if destination in {"email_password", "proxy_password"}:
			self.notebook.select(self.tabs["Notifications" if destination == "email_password" else "Settings"])
			self.editor.edit_passwords()
			return
		field = field_for_destination(destination)
		if field:
			self.notebook.select(self.tabs[field.tab])
			if field.tab == "Advanced" or field.dialog:
				self.editor.edit_options(field.key, group=field.dialog or "Advanced")

	def poll(self):
		if self.closed:
			return
		result = self.jobs.take()
		if result:
			name, value, error = result
			self.set_busy(False)
			if error:
				# ConfigParser and OS exceptions can contain raw file contents or
				# private paths. Keep the visible failure generic for this preview.
				self.status.set(str(error) if isinstance(error, (WorkspaceError, ControllerError)) else "Preview failed; check the directory, configuration and Python environment.")
				self.log("Local operation failed. Check the status message; reload before retrying a save.")
			elif name == "capabilities":
				self.options = value["cli_options"]
				self.filter_options()
				self.log("Offline backend ready; CLI reference loaded.")
			elif name == "workspace":
				self.display_workspace(value["snapshot"])
				self.editor.load(value["document"])
				self.set_busy(False)
			elif name == "save":
				self.editor.load(value["document"])
				self.status.set("Configuration saved locally" + ("; backup created. " if value["backup"] else ". ") + "Refresh preview to update displayed assignments. No server contacted.")
				self.log("Local configuration saved" + (" with a backup." if value["backup"] else "."))
				self.set_busy(False)
		while True:
			try:
				message = self.monitor.events.get_nowait()
			except queue.Empty:
				break
			if message.get("generation") != self.monitor.generation:
				continue
			event = message["event"]
			if event == "ready":
				self.log("Scheduled runner ready; interval {} seconds.".format(message["interval"]))
				if message.get("backup_created"):
					self.log("A private configuration backup was created before monitoring.")
			elif event == "cycle_started":
				if self.monitor.state != "Stopping":
					self.update_monitor_state("Running cycle")
				self.log("AutoPrimeNet communication cycle started.")
			elif event == "cycle_finished":
				if self.monitor.state != "Stopping":
					self.update_monitor_state("Waiting", "Last local cycle ended: {}\nNext cycle planned: {}".format(time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(message["time"])), time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(message["next_cycle"]))))
				self.log("CLI cycle exited zero; individual server outcomes remain unverified. Consult the AutoPrimeNet log.")
			elif event == "failed":
				self.update_monitor_state("Failed", message.get("error", "Check the workspace, locks and AutoPrimeNet log; reload before retrying."))
				self.log("Scheduled monitoring failed.")
			elif event == "stopped":
				self.update_monitor_state("Stopped", "Forced stop; inspect runtime files and sidecar locks." if message.get("forced") else "Stopped at a cycle boundary. Refresh before editing or restarting.")
			elif event == "exited":
				if self.monitor.state not in {"Failed", "Stopped"}:
					self.update_monitor_state("Failed", "The scheduled runner exited unexpectedly.")
				self.set_busy(self.jobs.busy)
				if self.quit_pending:
					self.finish_quit()
		if self.closed:
			return
		while True:
			try:
				event = self.tray.events.get_nowait()
			except queue.Empty:
				break
			if event == "ready":
				self.tray.ready = True
				self.tray.set_state(self.monitor.state)
				self.tray_status.set("Tray/menu bar ready. Close hides the window; use its menu to reopen.")
			elif event == "open":
				self.show()
			elif event == "quit":
				self.quit()
			elif event == "start":
				self.start_monitoring()
			elif event == "stop":
				self.stop_monitoring()
			else:
				self.tray.ready = False
				self.tray_status.set("Tray unavailable. Close minimizes to the taskbar/Dock.")
				if self.hidden:
					self.show()
			if self.closed:
				return
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
		# Finish bounded local operations, then stop owned monitoring at a cycle
		# boundary. Closing the window instead retains background monitoring.
		if self.jobs.busy:
			self.show()
			self.status.set("A local preview is still running; quit when it completes.")
			return
		if not self.discard_changes():
			return
		if self.monitor.active:
			self.show()
			if messagebox.askyesno("Quit and stop monitoring", "Stop scheduled monitoring and quit after the current CLI cycle finishes? Closing the window instead keeps monitoring in the background.", parent=self.root):
				self.quit_pending = True
				self.stop_monitoring()
			return
		self.finish_quit()

	def finish_quit(self):
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
