"""Workspace computation profile editor and explicit terminal launch controls.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import copy
from pathlib import Path
import time
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from gui_computation import launch_computation, prepare_launch, session_status
from gui_controller import BackgroundJobs
from gui_computation import FILENAME, LaunchError, PROGRAMS, TERMINALS, defaults, load_settings, save_settings


def parse_arguments(text):
	return text.removesuffix("\n").split("\n") if text else []


class LauncherView:
	def __init__(self, app):
		self.app = app
		self.jobs = BackgroundJobs()
		self.directory = None
		self.program = "Mlucas"
		self.settings, self.version = defaults(), None
		self.available = False
		self.window = None
		self.pending = None
		self.profile_name = tk.StringVar()
		self.status = tk.StringVar(value="Choose a working directory to load its computation launch profiles.")
		self.status.trace_add("write", lambda *_: self.app.status.set(self.status.get()))
		frame = app.tabs["Launchers"]
		ttk.Label(frame, text="Computation launch profiles", font=("TkDefaultFont", 14, "bold")).pack(anchor="w")
		ttk.Label(frame, text="Profiles belong to the selected workspace. Each starts one engine invocation in an independent terminal.\nStart computation is separate from Start monitoring. Closing or quitting the GUI leaves computations running.\nStop this worker in terminal. Engine configuration controls workers and GPUs; supply any required startup arguments explicitly.", wraplength=920, justify="left").pack(anchor="w", pady=8)
		controls = ttk.Frame(frame)
		controls.pack(fill="x")
		self.buttons = []
		for title, command in (("Add profile…", self.add), ("Edit selected…", self.edit), ("Delete selected…", self.delete), ("Reload launchers", self.reload)):
			button = ttk.Button(controls, text=title, command=command)
			button.pack(side="left", padx=(0, 6))
			self.buttons.append(button)
		self.table = ttk.Treeview(frame, columns=("Name", "Program", "Working directory", "Terminal"), show="headings", height=6)
		for column in self.table["columns"]:
			self.table.heading(column, text=column)
			self.table.column(column, width=160, minwidth=80)
		self.table.bind("<<TreeviewSelect>>", self.selected)
		self.table.bind("<Double-1>", lambda _event: self.edit())
		ttk.Label(frame, textvariable=self.status, wraplength=920, justify="left").pack(anchor="w", pady=6)
		self.launch_button = ttk.Button(controls, text="Start computation…", command=self.start)
		self.launch_button.pack(side="left")
		self.table.pack(fill="both", expand=True, pady=8)
		self.dashboard_selector = None
		self.dashboard_button = None

	def build_dashboard(self, frame):
		controls = ttk.Frame(frame)
		controls.pack(anchor="w", fill="x", pady=6)
		ttk.Label(controls, text="Computation profile").pack(side="left")
		self.dashboard_selector = ttk.Combobox(controls, textvariable=self.profile_name, state="readonly", width=24)
		self.dashboard_selector.pack(side="left", padx=6)
		self.dashboard_button = ttk.Button(controls, text="Start computation…", command=self.start)
		self.dashboard_button.pack(side="left")
		ttk.Button(controls, text="Manage launchers…", command=lambda: self.app.notebook.select(self.app.tabs["Launchers"])).pack(side="left", padx=6)

	def set_busy(self, busy=False):
		enabled = self.available and not busy and not self.jobs.busy and not self.app.quit_pending
		for button in self.buttons:
			button.state(["!disabled"] if enabled else ["disabled"])
		# Reload remains available to recover an externally repaired settings file.
		self.buttons[-1].state(["!disabled"] if self.directory and not busy and not self.jobs.busy and not self.app.quit_pending else ["disabled"])
		for button in (self.launch_button, self.dashboard_button):
			if button is not None:
				button.state(["!disabled"] if enabled and self.settings["profiles"] and not self.pending else ["disabled"])

	def set_workspace(self, snapshot):
		directory = str(Path(snapshot["directory"]).resolve())
		self.program = next((name for name in PROGRAMS if name.casefold() == snapshot.get("engine", self.program).casefold()), self.program)
		try:
			if any(Path(worker["work_file"]).resolve() == Path(directory) / FILENAME for worker in snapshot["workers"]):
				raise LaunchError("The work filename conflicts with the GUI launcher settings filename.")
			settings, version = load_settings(directory)
		except (OSError, ValueError):
			self.close_editor()
			self.directory, self.available = directory, False
			self.settings, self.version = defaults(), None
			self.status.set("Launcher settings could not be read. Repair or move " + FILENAME + ", then Reload launchers.")
			self.display()
			return
		if self.directory == directory and self.available and version == self.version:
			return
		self.close_editor()
		self.directory, self.available = directory, True
		self.settings, self.version = settings, version
		self.status.set("Profiles: " + str(Path(directory) / FILENAME) + ". Select or add a profile; loading never starts computation.")
		self.display()

	def reload(self):
		if self.directory and not self.jobs.busy:
			if self.window and self.window.winfo_exists() and not messagebox.askyesno("Reload launchers", "Discard the open profile edits and reload launchers?", parent=self.window):
				return
			self.available = False
			self.set_workspace({"directory": self.directory, "workers": self.app.progress_view.configured["workers"] if self.app.progress_view.configured else []})

	def display(self):
		self.table.delete(*self.table.get_children())
		for index, profile in enumerate(self.settings["profiles"]):
			self.table.insert("", "end", iid=str(index), values=(profile["name"], profile["program"], profile["directory"] or ".", profile["terminal"]))
		names = [profile["name"] for profile in self.settings["profiles"]]
		if self.profile_name.get() not in names:
			self.profile_name.set(names[0] if names else "")
		if self.dashboard_selector is not None:
			self.dashboard_selector.configure(values=names)
		self.app.progress_view.set_interval(self.settings["refresh_seconds"], self.available)
		self.set_busy(self.app.jobs.busy)

	def selected(self, _event=None):
		selection = self.table.selection()
		if selection:
			self.profile_name.set(self.settings["profiles"][int(selection[0])]["name"])

	def current(self):
		return next((profile for profile in self.settings["profiles"] if profile["name"] == self.profile_name.get()), None)

	def persist(self, settings):
		if not self.directory or not self.available:
			raise LaunchError("Choose a workspace with readable launcher settings first.")
		self.settings, self.version = save_settings(self.directory, settings, self.version)
		self.display()

	def save_interval(self, seconds):
		settings = copy.deepcopy(self.settings)
		settings["refresh_seconds"] = seconds
		try:
			self.persist(settings)
		except (OSError, ValueError) as error:
			messagebox.showerror("Progress refresh", str(error), parent=self.app.root)
			return False
		return True

	def add(self):
		self.open_editor(None)

	def edit(self):
		profile = self.current()
		if profile is not None:
			self.open_editor(profile)

	def open_editor(self, profile):
		if not self.available or self.jobs.busy or self.app.jobs.busy or self.app.quit_pending:
			return
		if self.window and self.window.winfo_exists():
			self.window.lift()
			return
		original = copy.deepcopy(profile)
		values = profile or {"name": "", "program": self.program, "executable": "", "directory": "", "terminal": "auto", "arguments": []}
		window = self.window = tk.Toplevel(self.app.root)
		window.title("Edit computation profile" if profile else "Add computation profile")
		window.geometry("700x590")
		window.transient(self.app.root)
		outer = ttk.Frame(window, padding=12)
		outer.pack(fill="both", expand=True)
		outer.columnconfigure(1, weight=1)
		variables = {key: tk.StringVar(value=values[key]) for key in ("name", "program", "executable", "directory", "terminal")}
		for index, (key, label) in enumerate((("name", "Profile name"), ("program", "Program"), ("executable", "Executable"), ("directory", "Working directory"), ("terminal", "Terminal"))):
			ttk.Label(outer, text=label).grid(row=index, column=0, sticky="w", pady=5)
			if key in {"program", "terminal"}:
				widget = ttk.Combobox(outer, textvariable=variables[key], values=PROGRAMS if key == "program" else TERMINALS, state="readonly")
			else:
				widget = ttk.Entry(outer, textvariable=variables[key])
			widget.grid(row=index, column=1, sticky="ew", padx=6)
			if key in {"executable", "directory"}:
				def browse(key=key):
					picker = filedialog.askopenfilename if key == "executable" else filedialog.askdirectory
					if path := picker(parent=window, initialdir=self.directory):
						variables[key].set(path)
				ttk.Button(outer, text="Browse…", command=browse).grid(row=index, column=2)
		ttk.Label(outer, text="Arguments: one exact argument per line; no shell quoting.\nBlank working directory uses this workspace; relative paths start here.\nKeep engine worker/GPU settings in the engine configuration or explicit arguments.\nProfiles store arguments as plain text; avoid passwords or other secrets.", wraplength=640, justify="left").grid(row=5, column=0, columnspan=3, sticky="w", pady=10)
		arguments = tk.Text(outer, height=7, wrap="none")
		arguments.grid(row=6, column=0, columnspan=3, sticky="nsew")
		outer.rowconfigure(6, weight=1)
		arguments.insert("1.0", "".join(argument + "\n" for argument in values["arguments"]))
		def save():
			item = {key: variable.get().strip() for key, variable in variables.items()}
			item["arguments"] = parse_arguments(arguments.get("1.0", "end-1c"))
			settings = copy.deepcopy(self.settings)
			if original:
				index = next((index for index, value in enumerate(settings["profiles"]) if value == original), None)
				if index is None:
					messagebox.showerror("Profile changed", "Reload launchers and reopen this profile.", parent=window)
					return
				settings["profiles"][index] = item
			else:
				settings["profiles"].append(item)
			try:
				self.persist(settings)
			except (OSError, ValueError) as error:
				messagebox.showerror("Save launch profile", str(error), parent=window)
				return
			self.profile_name.set(item["name"])
			self.close_editor()
		controls = ttk.Frame(outer)
		controls.grid(row=7, column=0, columnspan=3, sticky="w", pady=(12, 0))
		ttk.Button(controls, text="Save profile", command=save).pack(side="left")
		ttk.Button(controls, text="Cancel", command=self.close_editor).pack(side="left", padx=8)
		self.editor_variables, self.editor_arguments, self.editor_save = variables, arguments, save
		self.editor_original = copy.deepcopy(values)

	@property
	def dirty(self):
		if not self.window or not self.window.winfo_exists():
			return False
		values = {key: variable.get().strip() for key, variable in self.editor_variables.items()}
		values["arguments"] = parse_arguments(self.editor_arguments.get("1.0", "end-1c"))
		return values != self.editor_original

	def close_editor(self):
		if self.window and self.window.winfo_exists():
			self.window.destroy()
		self.window = None

	def delete(self):
		profile = self.current()
		if profile and messagebox.askyesno("Delete launch profile", "Delete profile '" + profile["name"] + "'? Running computations and engine files are unaffected.", parent=self.app.root):
			settings = copy.deepcopy(self.settings)
			settings["profiles"].remove(profile)
			try:
				self.persist(settings)
			except (OSError, ValueError) as error:
				messagebox.showerror("Delete launch profile", str(error), parent=self.app.root)

	def start(self):
		profile = self.current()
		if profile is None or self.jobs.busy or self.app.jobs.busy or self.pending or not self.available or self.app.quit_pending:
			return
		if self.window and self.window.winfo_exists():
			self.window.lift()
			self.status.set("Save or cancel the open launch profile before starting computation.")
			return
		self.launch_profile = copy.deepcopy(profile)
		self.launch_base, self.launch_version = self.directory, self.version
		self.jobs.submit("prepare", prepare_launch, self.launch_base, self.launch_profile, self.launch_version)
		self.status.set("Checking executable, working directory, terminal and existing processes…")
		self.app.set_busy(self.app.jobs.busy)

	def tick(self):
		result = self.jobs.take()
		if result:
			name, value, error = result
			if error:
				self.status.set("Computation launch failed. " + str(error))
				messagebox.showerror("Start computation", str(error), parent=self.app.root)
			elif name == "prepare":
				plan = value["plan"]
				text = "Profile: " + plan["name"] + "\nProgram: " + plan["program"] + "\nExecutable: " + plan["argv"][0] + "\nDirectory: " + plan["directory"] + "\nTerminal: " + value["terminal"] + "\nArguments (one per line):\n" + ("\n".join(plan["argv"][1:]) or "(none)")
				text += "\n\nThis starts computation in an independent terminal. It continues after the GUI closes. It does not start AutoPrimeNet monitoring."
				if value["inaccessible"]:
					text += "\nSome processes could not be inspected; duplicate detection is incomplete."
				if self.directory == self.launch_base and not self.app.quit_pending and messagebox.askyesno("Start computation", text, parent=self.app.root):
					self.jobs.submit("launch", launch_computation, self.launch_base, self.launch_profile, self.launch_version, value)
				else:
					self.status.set("Computation launch cancelled.")
			else:
				self.pending = {**value, "deadline": time.monotonic() + 30}
				self.status.set("Terminal requested. Waiting for the computation helper to confirm startup…")
			self.app.set_busy(self.app.jobs.busy)
		if self.pending:
			try:
				state = session_status(self.pending["session"])
			except FileNotFoundError:
				state = {"state": "waiting"}
			except (OSError, ValueError):
				state = {"state": "failed"}
			phase = state.get("state")
			if phase in {"running", "finished", "failed"}:
				if phase == "running":
					self.status.set("Computation started (PID " + str(state["pid"]) + "). Progress shows the engine's latest saved data.")
				elif phase == "finished":
					self.status.set("Computation exited with status " + str(state["exit_code"]) + ". Review its terminal output.")
				else:
					self.status.set("The terminal request failed. Check terminal availability and OS automation permissions." if state.get("reason") == "terminal" else "Computation could not start. Review the terminal output for the error.")
				self.pending = None
				self.app.progress_view.refresh()
				self.set_busy(self.app.jobs.busy)
			elif time.monotonic() > self.pending["deadline"]:
				self.status.set("Startup was not confirmed within 30 seconds. Check the terminal and Progress before trying again.")
				self.pending = None
				self.set_busy(self.app.jobs.busy)

	def close(self):
		self.close_editor()
		self.jobs.close()
