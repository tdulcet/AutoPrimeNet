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
import textwrap
import time

try:
	import tkinter as tk
	from tkinter import filedialog, messagebox, simpledialog, ttk
except ImportError:
	print("Tkinter is unavailable. Install the Tk bindings matching this Python; see GUI.md.", file=sys.stderr)
	sys.exit(2)

from gui_config import WorkspaceError, load_editor_workspace, save_configuration, lock_policy_notice
from gui_controller import BackgroundJobs, ControllerError, MonitorController, TrayController, backend_request
from gui_forms import ConfigurationForms
from gui_options import field_for_destination
from gui_operations import OPERATIONS, operation_arguments, operation_for_destination
from gui_registration_form import RegistrationForm
from gui_reports import BackendLogWindow, export_debug_report
from gui_reference import reference_info
from gui_trace import trace_notice
from gui_preferences import preferences_path, read_workspace, remember_workspace


TABS = ("Dashboard", "Assignments", "Workers", "PrimeNet", "Advanced", "Notifications", "Logs & Status", "Settings")
WORK_TYPES = {2: "TF", 3: "P-1", 4: "P-1", 5: "ECM", 6: "P+1", 100: "LL", 101: "LL double-check", 150: "PRP", 200: "Certification"}


class Application:
	def __init__(self, root, tray=True, remember=True):
		self.root = root
		self.jobs = BackgroundJobs()
		self.tray = TrayController()
		self.monitor = MonitorController()
		self.active_operation = None
		self.native_monitor = False
		self.monitor_watch = False
		self.quit_pending = False
		self.hidden = False
		self.closed = False
		self.automatic_updates = True
		self.autosave_due = None
		self.refresh_pending = False
		self.automatic_document = None
		self.quit_after_save = False
		self.preferences_path = preferences_path() if remember else None
		self.restore_workspace = None
		preference_error = False
		if self.preferences_path is not None:
			try:
				self.restore_workspace = read_workspace(self.preferences_path)
			except (OSError, ValueError):
				preference_error = True
		self.options = []
		self.backend_version = "not loaded"
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
		if preference_error:
			self.log("Remembered workspace could not be read. Choose a working directory manually.")
		self.set_busy(False)
		if tray:
			self.tray.start()
		self.jobs.submit("capabilities", backend_request, "capabilities")
		self.poll_after = self.root.after(100, self.poll)

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
		help_menu.add_command(label="Original CLI help", command=self.request_cli_help)
		help_menu.add_command(label="About", command=self.show_about)
		menu.add_cascade(label="Help", menu=help_menu)
		self.root.config(menu=menu)
		# Reserve status space before the expanding notebook can consume it.
		self.status_label = ttk.Label(self.root, textvariable=self.status, relief="sunken", anchor="w", padding=5, wraplength=760)
		self.status_label.pack(fill="x", side="bottom")
		self.status_label.bind("<Configure>", lambda event: self.status_label.configure(wraplength=max(1, event.width - 12)))
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
		self.registration = RegistrationForm(self)
		self.backend_log = BackendLogWindow(self)
		self.operation_buttons = {}
		operation_frames, operation_counts = {}, {}
		for key, operation in OPERATIONS.items():
			if operation.tab not in operation_frames:
				frame = operation_frames[operation.tab] = ttk.Frame(self.tabs[operation.tab])
				frame.pack(anchor="w", fill="x", pady=(0, 6))
				operation_counts[operation.tab] = 0
			index = operation_counts[operation.tab]
			button = ttk.Button(operation_frames[operation.tab], text=operation.title + "…", command=lambda key=key: self.run_operation(key))
			button.grid(row=index // 2, column=index % 2, sticky="w", padx=(0, 8), pady=(0, 6))
			operation_counts[operation.tab] += 1
			self.operation_buttons[key] = button
		ttk.Label(self.tabs["Dashboard"], text="Local workspace", font=("TkDefaultFont", 16)).pack(anchor="w")
		ttk.Label(self.tabs["Dashboard"], textvariable=self.summary, justify="left", wraplength=720).pack(anchor="w", pady=12)
		ttk.Label(self.tabs["Dashboard"], textvariable=self.monitor_status, justify="left").pack(anchor="w")
		controls = ttk.Frame(self.tabs["Dashboard"])
		controls.pack(anchor="w", pady=8)
		self.start_button = ttk.Button(controls, text="Start monitoring…", command=self.start_monitoring)
		self.start_button.pack(side="left")
		self.stop_button = ttk.Button(controls, text="Stop after active work", command=self.stop_monitoring)
		self.stop_button.pack(side="left", padx=8)
		self.force_button = ttk.Button(controls, text="Force stop…", command=self.force_stop_monitoring)
		self.force_button.pack(side="left")
		ttk.Label(self.tabs["Dashboard"], textvariable=self.tray_status, wraplength=720).pack(anchor="w", pady=16)
		self.assignments = self._table(self.tabs["Assignments"], ("Worker", "Exponent", "Work type", "Local AID", "Server confirmation"))
		ttk.Label(self.tabs["Assignments"], text="The table is a read-only preview. Parsed work lines and local AIDs do not confirm current server reservations. Actions above require confirmation.", wraplength=720).pack(anchor="w", pady=8)
		self.workers = self._table(self.tabs["Workers"], ("Worker", "Directory", "Preference", "Work file"))
		for name, explanation in (
			("PrimeNet", "Save settings before registering/updating this computer. Ping and v6 ping contact the selected API once; Dashboard starts scheduled monitoring. Computer registration synchronizes program options without requesting work."),
			("Notifications", "Save notification settings locally with Save settings. Blank boolean values use the backend default. Monitoring and confirmed test-email actions can send messages. Manage passwords to replace or remove SMTP/proxy passwords; replacements require encryption. Set Send configured notifications to False to suppress sending."),
		):
			ttk.Label(self.tabs[name], text=explanation, wraplength=720, justify="left").pack(anchor="w")
		ttk.Label(self.tabs["Advanced"], text="Search CLI flags, graphical locations and coverage. Full parity remains unfinished; see GUI_PARITY.md.").pack(anchor="w")
		entry = ttk.Entry(self.tabs["Advanced"], textvariable=self.search)
		entry.pack(fill="x", pady=8)
		self.search.trace_add("write", lambda *_: self.filter_options())
		self.reference = self._table(self.tabs["Advanced"], ("CLI flags", "Destination", "GUI location", "Coverage"))
		self.reference.bind("<Double-1>", self.open_reference_setting)
		self.reference.bind("<Return>", self.open_reference_setting)
		reports = ttk.Frame(self.tabs["Logs & Status"])
		reports.pack(fill="x", pady=(0, 8))
		self.backend_log_button = ttk.Button(reports, text="View private backend log…", command=self.backend_log.open)
		self.backend_log_button.pack(side="left")
		self.trace_button = ttk.Button(reports, text="View latest private trace…", command=self.backend_log.open_trace)
		self.trace_button.pack(side="left", padx=8)
		self.diagnostics_button = ttk.Button(reports, text="Export private diagnostics…", command=self.request_diagnostics)
		self.diagnostics_button.pack(side="left", padx=8)
		self.activity = tk.Text(self.tabs["Logs & Status"], wrap="word", state="disabled", height=12)
		self.activity.pack(fill="both", expand=True)
		ttk.Label(self.tabs["Logs & Status"], text="GUI activity below. Native logs open separately and may contain private details; diagnostic exports require review before sharing.", wraplength=900).pack(anchor="w", pady=8)
		ttk.Label(self.tabs["Settings"], text="Configuration filename (reload after changing)").pack(anchor="w")
		self.config_entry = ttk.Entry(self.tabs["Settings"], textvariable=self.config_name, width=40)
		self.config_entry.pack(anchor="w", pady=8)
		self.retry_tray_button = ttk.Button(self.tabs["Settings"], text="Retry tray integration", command=self.retry_tray)
		self.retry_tray_button.pack(anchor="w", pady=8)
		ttk.Label(self.tabs["Settings"], text="Valid edits save automatically after a short pause, once editor dialogs close.\nCompleted operations refresh the workspace automatically.\nClosing hides to the tray/menu bar when ready; otherwise it minimizes.\nUse File → Quit to exit.\nSee GUI.md for setup and requirements.", justify="left", wraplength=720).pack(anchor="w", pady=12)

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
		if self.jobs.busy or self.monitor.active or self.quit_pending:
			return
		directory = filedialog.askdirectory(parent=self.root, title="Choose AutoPrimeNet working directory")
		if directory and self.discard_changes():
			self.directory.set(directory)
			self.refresh(confirm_discard=False)

	def discard_changes(self):
		return not (self.editor.dirty or self.registration.dirty) or messagebox.askyesno("Unsaved changes", "Discard unsaved configuration or queued registration edits?", parent=self.root)

	def set_busy(self, busy):
		active = self.monitor.active
		self.reload_button.state(["disabled"] if busy or self.quit_pending else ["!disabled"])
		for widget in (self.browse_button, self.directory_entry, self.config_entry):
			widget.state(["disabled"] if busy or active or self.quit_pending else ["!disabled"])
		self.editor.set_enabled(not busy and not active and not self.quit_pending and self.editor.document is not None)
		self.registration.set_busy(busy or active or self.quit_pending)
		self.backend_log.set_busy(busy or self.quit_pending)
		self.backend_log_button.state(["disabled"] if busy or self.quit_pending or self.editor.document is None else ["!disabled"])
		self.trace_button.state(["disabled"] if busy or self.quit_pending or self.editor.document is None else ["!disabled"])
		self.diagnostics_button.state(["disabled"] if busy or active or self.quit_pending or self.editor.document is None else ["!disabled"])
		self.save_button.state(["disabled"] if busy or active or self.quit_pending or self.editor.document is None else ["!disabled"])
		self.start_button.state(["disabled"] if busy or active or self.quit_pending or self.editor.document is None else ["!disabled"])
		for button in self.operation_buttons.values():
			button.state(["disabled"] if busy or active or self.quit_pending or self.editor.document is None else ["!disabled"])
		self.stop_button.state(["!disabled"] if active and self.monitor.state != "Stopping" else ["disabled"])
		self.force_button.state(["!disabled"] if active else ["disabled"])

	def refresh(self, confirm_discard=True):
		if self.jobs.busy or self.quit_pending or not self.directory.get().strip() or (confirm_discard and not self.discard_changes()):
			return
		if self.jobs.submit("workspace", load_editor_workspace, self.directory.get(), self.config_name.get()):
			self.status.set("Reading local workspace…")
			self.set_busy(True)

	def schedule_autosave(self):
		if self.automatic_updates:
			self.autosave_due = time.monotonic() + 2

	def remember_selection(self, document):
		if self.preferences_path is not None:
			try:
				remember_workspace(self.preferences_path, document)
			except (OSError, ValueError):
				self.log("Workspace is loaded, but its selection could not be remembered for next launch.")

	def editor_dialog_open(self):
		return any(window is not None and window.winfo_exists() for window in (
			self.editor.options_window, self.editor.password_window,
			self.editor.mail_window, self.editor.worker_window, self.registration.window,
		))

	def automatic_update(self):
		if not self.automatic_updates or self.closed or self.quit_pending or self.jobs.busy or self.monitor.active or self.editor_dialog_open():
			return
		if self.refresh_pending:
			if self.editor.dirty:
				self.refresh_pending = False
				self.log("Automatic refresh paused to preserve unsaved configuration. Reload explicitly before saving if the backend changed it.")
				return
			document = self.editor.document
			if document is None:
				self.refresh_pending = False
				return
			if Path(self.directory.get()).expanduser().resolve() != document.directory or self.config_name.get() != document.path.name:
				self.refresh_pending = False
				return
			if self.jobs.submit("automatic_workspace", load_editor_workspace, str(document.directory), document.path.name):
				self.refresh_pending = False
				self.automatic_document = document
				self.set_busy(True)
		elif self.autosave_due is not None and time.monotonic() >= self.autosave_due:
			self.autosave_due = None
			if self.editor.dirty:
				self.save(automatic=True)

	def save(self, automatic=False):
		self.autosave_due = None
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
			if automatic:
				messagebox.showerror("Configuration was not saved", str(error), parent=self.root)
			return
		if not automatic and not messagebox.askyesno("Save local configuration", ("" if values["require_lock"] != "False" else "Native-lock success is not required for this save. Verify no independent AutoPrimeNet uses this workspace.\n\n") + "Validate and save the displayed settings locally? An existing configuration will be backed up. No server will be contacted. Stop any independently running AutoPrimeNet before saving.", parent=self.root):
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
		if self.registration.dirty:
			self.status.set("Finish or discard the queued registration batch before starting monitoring.")
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
			self.status.set("Correct and save the progress check-in and polling intervals before starting monitoring.")
			return
		try:
			interval = document.config.getint("GUI", "PollSeconds", fallback=3600)
			watch = document.config.getboolean("PrimeNet", "watch", fallback=True)
			if interval < 0 or (interval != 0 and not 1800 <= interval <= hours * 3600):
				raise ValueError
		except ValueError:
			self.status.set("Polling must be 0 or at least 1800 seconds, and no longer than the progress check-in interval.")
			return
		try:
			trace_text = trace_notice(document) + lock_policy_notice(document.config)
		except ValueError:
			self.status.set("Correct and save debug verbosity or instance-lock policy before running AutoPrimeNet.")
			return
		cadence = "Run one complete pass, then stop." if interval == 0 else f"Poll every {interval} seconds; report progress every {hours} hour(s). " + ("Watch results and proof files immediately." if watch else "Check results and proofs at each poll.")
		if not messagebox.askyesno("Start monitoring", cadence + trace_text + "\n\nAutoPrimeNet can register/update this computer, request/register assignments, report results/progress, download certification data, upload proofs and send configured notifications. Uploaded proofs are archived or deleted according to the saved configuration.\n\nStop finishes active work and waits for reporting/upload workers to exit. Computation engines are never started or stopped.", parent=self.root):
			return
		try:
			self.monitor.start(document)
		except ControllerError as error:
			self.set_busy(self.jobs.busy)
			self.status.set(str(error))
			return
		self.active_operation = None
		self.update_monitor_state("Starting")

	def run_operation(self, key, parameters=None):
		operation = OPERATIONS.get(key)
		if operation is None or self.jobs.busy or self.monitor.active or self.quit_pending or self.editor.document is None:
			return
		self.show()
		if self.editor.dirty:
			self.status.set("Save or reload unsaved changes before running an operation.")
			return
		if key != "register_exponents" and self.registration.dirty:
			self.status.set("Finish or discard the queued registration batch before running another operation.")
			return
		document = self.editor.document
		if Path(self.directory.get()).expanduser().resolve() != document.directory or self.config_name.get() != document.path.name:
			self.status.set("Reload the selected workspace before running an operation.")
			return
		if document.version is None:
			self.status.set("Save the configuration before running an operation.")
			return
		if key == "register_exponents" and parameters is None:
			self.registration.open()
			return
		parameters = {} if parameters is None else parameters
		if operation.requires_exponent:
			initial = None
			selected = self.assignments.selection()
			if selected:
				try:
					initial = int(self.assignments.item(selected[0], "values")[1])
				except (ValueError, TypeError):
					pass
			exponent = simpledialog.askinteger(operation.title, "Exponent to unreserve (the CLI uses the first match across workers, not a selected AID):", initialvalue=initial, minvalue=2, maxvalue=9999999999, parent=self.root)
			if exponent is None:
				return
			parameters["exponent"] = exponent
		command = " ".join((*operation_arguments(key, parameters), "--timeout", "0"))
		prompt = operation.effects + "\n\nRun once for the selected workspace? The CLI can update its configuration and runtime files. A private configuration backup is created first; it does not roll back server actions or proof/result changes.\n\nCLI options: " + command + "\n\nCompletion alone does not confirm server acceptance or message delivery. Check the AutoPrimeNet log. Stop waits for this command to finish; computation engines are not started or stopped."
		try:
			prompt += trace_notice(document) + lock_policy_notice(document.config)
		except ValueError:
			self.status.set("Correct and save debug verbosity or instance-lock policy before running AutoPrimeNet.")
			return
		if key == "register_exponents":
			prompt += "\n\nWorker: {}. Batch size: {}. Review the offline work-line preview before continuing.".format(parameters["worker"], len(parameters["entries"]))
		if operation.confirmation:
			phrase = operation.confirmation + (" " + str(parameters["exponent"]) if operation.requires_exponent else "")
			if key == "register_exponents":
				phrase += " " + str(len(parameters["entries"]))
			prompt += "\n\nPrivate snapshots of work/certification files are required before launch. Pause affected computation engines; snapshots cannot prevent later file changes or undo reservation releases.\n\nType " + phrase + " to proceed:"
			wrapped = "\n".join(textwrap.fill(line, width=88) for line in prompt.splitlines())
			confirmed = simpledialog.askstring(operation.title, wrapped, parent=self.root) == phrase
		else:
			confirmed = messagebox.askyesno(operation.title, prompt, parent=self.root)
		if not confirmed:
			return
		try:
			self.monitor.start(document, operation=key, parameters=parameters)
		except ControllerError as error:
			self.set_busy(self.jobs.busy)
			self.status.set(str(error))
			return
		self.active_operation = key
		self.update_monitor_state("Starting")
		return True

	def update_monitor_state(self, state, detail=""):
		self.monitor.state = state
		label = OPERATIONS[self.active_operation].title if self.active_operation else "Scheduled monitoring"
		self.status.set(label + ": " + state)
		self.monitor_status.set(label + ": " + state + ("\n" + detail if detail else "") + "\nServer acceptance/connectivity: unverified")
		self.tray.set_state(state)
		self.set_busy(self.jobs.busy)

	def request_diagnostics(self):
		if self.jobs.busy or self.monitor.active or self.quit_pending or self.editor.document is None:
			return
		document = self.editor.document
		if self.editor.dirty or Path(self.directory.get()).expanduser().resolve() != document.directory or self.config_name.get() != document.path.name:
			self.status.set("Save/reload the selected configuration before exporting diagnostics.")
			return
		if not messagebox.askyesno("Private diagnostic report", "Create a private diagnostic file in this workspace using the original backend? It contains account, computer and hardware identifiers. Review/redact before sharing.\n\nNo network access is permitted. Configuration, assignment and engine files are not changed.", parent=self.root):
			return
		if self.jobs.submit("debug_report", export_debug_report, document):
			self.set_busy(True)
			self.status.set("Generating private diagnostics offline…")

	def show_about(self):
		messagebox.showinfo("About AutoPrimeNet GUI", "Optional GUI foundation\nBackend AutoPrimeNet {}\nPython 3.15.0 or later\nGPL-3.0\n\nSee GUI_PARITY.md for implemented controls and remaining gaps.".format(self.backend_version), parent=self.root)

	def request_cli_help(self):
		if not self.jobs.busy and not self.quit_pending and self.jobs.submit("cli_help", backend_request, "cli_help"):
			self.set_busy(True)

	def show_text_report(self, title, text):
		window = tk.Toplevel(self.root)
		window.title(title)
		window.geometry("900x600")
		frame = ttk.Frame(window, padding=10)
		frame.pack(fill="both", expand=True)
		widget = tk.Text(frame, wrap="word")
		scrollbar = ttk.Scrollbar(frame, orient="vertical", command=widget.yview)
		widget.configure(yscrollcommand=scrollbar.set)
		scrollbar.pack(side="right", fill="y")
		widget.pack(fill="both", expand=True)
		widget.insert("end", text)
		widget.configure(state="disabled")
		return window

	def stop_monitoring(self):
		if self.monitor.active:
			self.monitor.stop()
			self.update_monitor_state("Stopping", "Waiting for active work and reporting/upload workers to finish safely.")

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
			tab, label, coverage = reference_info(option["dest"])
			location = (tab + " → " if tab else "") + label
			if term in (flags + " " + option["dest"] + " " + location + " " + coverage).casefold():
				self.reference.insert("", "end", values=(flags, option["dest"], location, coverage))

	def open_reference_setting(self, _event=None):
		selected = self.reference.selection()
		if not selected:
			return
		destination = self.reference.item(selected[0], "values")[1]
		if destination == "version":
			self.show_about()
			return
		if destination == "help":
			self.request_cli_help()
			return
		if destination == "debug_info":
			self.notebook.select(self.tabs["Logs & Status"])
			self.diagnostics_button.focus_set()
			return
		operation = operation_for_destination(destination)
		if operation:
			self.notebook.select(self.tabs[OPERATIONS[operation].tab])
			self.operation_buttons[operation].focus_set()
			return
		if destination in {"email_password", "proxy_password"}:
			self.notebook.select(self.tabs["Notifications" if destination == "email_password" else "Settings"])
			self.editor.edit_passwords()
			return
		field = field_for_destination(destination)
		if field:
			self.notebook.select(self.tabs[field.tab])
			if field.tab == "Advanced" or field.dialog:
				self.editor.edit_options(field.key, group=field.dialog or "Advanced")
		else:
			tab, _label, _coverage = reference_info(destination)
			if tab:
				self.notebook.select(self.tabs[tab])
			if destination == "workdir":
				self.directory_entry.focus_set()
			elif destination == "localfile":
				self.config_entry.focus_set()

	def poll(self):
		self.poll_after = None
		if self.closed:
			return
		result = self.jobs.take()
		if result:
			name, value, error = result
			self.set_busy(False)
			if name == "registration_preview":
				self.registration.complete_preview(value, error)
			elif name == "discover_gpus":
				self.editor.complete_gpus(value, error)
			elif name == "discover_mail":
				self.editor.complete_mail(value, error)
			elif name == "backend_log":
				self.backend_log.complete(value, error)
			elif error:
				self.quit_after_save = False
				# ConfigParser and OS exceptions can contain raw file contents or
				# private paths. Keep the visible failure generic for this preview.
				self.status.set(str(error) if isinstance(error, (WorkspaceError, ControllerError)) else "Preview failed; check the directory, configuration and Python environment.")
				self.log("Local operation failed. Check the status message; reload before retrying a save.")
				if name == "save":
					messagebox.showerror("Configuration was not saved", self.status.get(), parent=self.root)
			elif name == "capabilities":
				self.backend_version = value["backend_version"]
				self.options = value["cli_options"]
				self.filter_options()
				self.log("Offline backend ready; CLI reference loaded.")
			elif name == "automatic_workspace":
				if self.editor.document is self.automatic_document and not self.editor.dirty:
					self.backend_log.close()
					self.editor.load(value["document"])
					self.registration.invalidate()
					self.display_workspace(value["snapshot"])
					self.status.set("Local configuration and workspace refreshed automatically. " + self.monitor.state)
					self.log("Local configuration and workspace refreshed automatically.")
				self.automatic_document = None
				self.set_busy(False)
			elif name == "workspace":
				self.registration.close()
				self.backend_log.close()
				self.display_workspace(value["snapshot"])
				self.editor.load(value["document"])
				self.remember_selection(value["document"])
				self.set_busy(False)
			elif name == "save":
				self.backend_log.close()
				self.editor.load(value["document"])
				self.status.set("Configuration saved locally" + ("; backup created. " if value["backup"] else ". ") + "No server contacted.")
				self.refresh_pending = self.automatic_updates
				self.log("Local configuration saved" + (" with a backup." if value["backup"] else "."))
				self.set_busy(False)
				if self.quit_after_save:
					self.quit_after_save = False
					self.quit()
					if self.closed:
						return
			elif name == "debug_report":
				self.status.set("Private diagnostics saved: " + value["path"])
				self.log("Private diagnostic report: " + value["path"] + ". Review/redact before sharing.")
			elif name == "cli_help":
				self.show_text_report("Original AutoPrimeNet CLI help", value["text"])
		while True:
			try:
				message = self.monitor.events.get_nowait()
			except queue.Empty:
				break
			if message.get("generation") != self.monitor.generation:
				continue
			event = message["event"]
			if event == "ready":
				self.native_monitor = message.get("native_scheduler", False)
				self.monitor_watch = message.get("watch", False)
				self.log("One-shot operation ready." if self.active_operation else "Monitoring runner ready; polling interval {} seconds.".format(message["interval"]))
				if message.get("native_lock_unverified"):
					self.log("Native lock acquisition was not verified. The atomic GUI ownership guard is active; independent CLI exclusion cannot be guaranteed.")
				if message.get("backup_created"):
					self.log("A private configuration backup was created before starting AutoPrimeNet.")
				if message.get("assignment_backup"):
					self.log("Private work/certification snapshot: " + message["assignment_backup"])
			elif event == "trace_created":
				self.log("Private raw trace file created: " + message["name"] + ". Review/redact before sharing.")
			elif event == "trace_warning":
				self.log("Private trace capture was incomplete. Check workspace disk space and permissions.")
			elif event == "cycle_started":
				if self.monitor.state != "Stopping":
					self.update_monitor_state("Running cycle")
				self.log((OPERATIONS[self.active_operation].title if self.active_operation else "AutoPrimeNet communication cycle") + " started.")
			elif event == "operation_finished":
				self.log("One-shot CLI exited zero; server acceptance and message delivery remain unverified. Consult the AutoPrimeNet log.")
			elif event == "cycle_finished":
				if self.monitor.state != "Stopping":
					self.update_monitor_state("Watching files" if self.native_monitor and self.monitor_watch else "Waiting", "Last local cycle ended: {}\nNext poll planned: {}".format(time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(message["time"])), time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(message["next_cycle"]))))
				self.log("Local cycle completed; individual server outcomes remain unverified. Consult the AutoPrimeNet log.")
			elif event == "failed":
				self.update_monitor_state("Failed", message.get("error", "Check the workspace, locks and AutoPrimeNet log; reload before retrying."))
				self.log("One-shot operation failed." if self.active_operation else "Scheduled monitoring failed.")
			elif event == "stopped":
				if message.get("forced"):
					detail = "Forced stop; inspect runtime files and sidecar locks."
				elif self.automatic_updates:
					detail = "Local operation ended; configuration and workspace will refresh automatically."
				else:
					detail = "One-shot command ended. Refresh before editing or running another command." if self.active_operation else "Stopped after active work finished. Refresh before editing or restarting."
				self.update_monitor_state("Stopped", detail)
			elif event == "exited":
				self.refresh_pending = self.automatic_updates
				if self.monitor.state not in {"Failed", "Stopped"}:
					self.update_monitor_state("Failed", "The scheduled runner exited unexpectedly.")
				self.set_busy(self.jobs.busy)
				if self.quit_pending:
					self.finish_quit()
		if self.closed:
			return
		while True:
			try:
				tray_message = self.tray.events.get_nowait()
			except queue.Empty:
				break
			if isinstance(tray_message, dict):
				if tray_message.get("generation") != self.tray.generation:
					continue
				event = tray_message["event"]
			else:
				event = tray_message
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
				self.tray.stop()
				self.tray_status.set("Tray unavailable. Close minimizes to the taskbar/Dock.")
				if self.hidden:
					self.show()
			if self.closed:
				return
		if not self.tray.ready and time.monotonic() > self.tray_deadline:
			self.tray_status.set("Tray unavailable. Close minimizes to the taskbar/Dock.")
			self.tray.stop()
		if not self.closed:
			if self.restore_workspace is not None and not self.jobs.busy:
				directory, name = self.restore_workspace
				self.restore_workspace = None
				if self.editor.document is None and not self.directory.get():
					self.directory.set(directory)
					self.config_name.set(name)
					self.refresh(confirm_discard=False)
			self.automatic_update()
			self.poll_after = self.root.after(100, self.poll)

	def retry_tray(self):
		if self.quit_pending or self.closed:
			return
		if self.tray.process is not None and self.tray.process.poll() is None:
			if self.tray.ready:
				self.tray_status.set("Tray/menu bar is already available.")
			else:
				self.tray_status.set("Tray helper is still starting. Close the GUI only after tray readiness is confirmed.")
			return
		self.tray_deadline = time.monotonic() + 15
		self.tray_status.set("Retrying tray integration; the window remains reachable until ready.")
		self.tray.start()

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
			self.status.set("An operation is still running; quit when it completes.")
			return
		if self.automatic_updates and self.editor.dirty and not self.monitor.active and not self.editor_dialog_open():
			self.save(automatic=True)
			self.quit_after_save = self.jobs.busy
			return
		if not self.discard_changes():
			return
		if self.monitor.active:
			self.show()
			if messagebox.askyesno("Quit and stop AutoPrimeNet", "Stop the GUI-owned AutoPrimeNet runner and quit after active work and reporting/upload workers finish? Closing the window instead keeps it running in the background.", parent=self.root):
				self.quit_pending = True
				self.stop_monitoring()
			return
		self.finish_quit()

	def finish_quit(self):
		self.closed = True
		if self.poll_after is not None:
			self.root.after_cancel(self.poll_after)
			self.poll_after = None
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
