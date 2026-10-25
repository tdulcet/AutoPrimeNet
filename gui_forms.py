"""Graphical configuration fields and worker editing.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from gui_config import ENGINES
from gui_options import FIELDS, validate_fields
from gui_controller import backend_request


class ConfigurationForms:
	def __init__(self, app):
		self.app = app
		self.document = None
		self.loading = False
		self.dirty = False
		self.widgets = []
		self.values = {}
		self.engine = tk.StringVar()
		self.count = tk.StringVar(value="1")
		self.worker_values = []
		self.options_window = None
		self.options_values = {}
		self.gpu_target = None
		self.credentials = {}
		self.password_window = None
		for field in FIELDS:
			variable = tk.StringVar(value=field.default)
			variable.trace_add("write", self.changed)
			self.values[field.key] = variable
		for tab in dict.fromkeys(field.tab for field in FIELDS):
			if tab == "Advanced":
				button = ttk.Button(app.tabs[tab], text="Edit advanced assignment settings…", command=self.edit_options)
				button.pack(anchor="w", pady=(0, 8))
				self.widgets.append(button)
				continue
			frame = ttk.LabelFrame(app.tabs[tab], text="Local configuration", padding=8)
			frame.pack(fill="x", pady=(0, 8))
			frame.columnconfigure(1, weight=1)
			for row, field in enumerate(field for field in FIELDS if field.tab == tab and not field.dialog):
				variable = self.values[field.key]
				ttk.Label(frame, text=field.label).grid(row=row, column=0, sticky="w", padx=(0, 8), pady=2)
				if field.kind == "boolean":
					widget = ttk.Combobox(frame, textvariable=variable, values=("", "True", "False"), state="readonly", width=12)
				else:
					widget = ttk.Entry(frame, textvariable=variable)
				widget.grid(row=row, column=1, sticky="ew", pady=2)
				self.widgets.append(widget)
		button = ttk.Button(app.tabs["PrimeNet"], text="Edit hardware and resource settings…", command=lambda: self.edit_options(group="Hardware"))
		button.pack(anchor="w", pady=(0, 8))
		self.widgets.append(button)
		button = ttk.Button(app.tabs["Settings"], text="Edit update and output preferences…", command=lambda: self.edit_options(group="Behavior"))
		button.pack(anchor="w", pady=(0, 8))
		self.widgets.append(button)
		button = ttk.Button(app.tabs["Settings"], text="Edit connection settings…", command=lambda: self.edit_options(group="Connection"))
		button.pack(anchor="w", pady=(0, 8))
		self.widgets.append(button)
		for tab in ("Settings", "Notifications"):
			button = ttk.Button(app.tabs[tab], text="Manage SMTP and proxy passwords…", command=self.edit_passwords)
			button.pack(anchor="w", pady=(0, 8))
			self.widgets.append(button)
		frame = ttk.LabelFrame(app.tabs["Workers"], text="Program and worker configuration", padding=8)
		frame.pack(fill="x", pady=(0, 8))
		ttk.Label(frame, text="Computation program").grid(row=0, column=0, sticky="w")
		program = ttk.Combobox(frame, textvariable=self.engine, values=ENGINES, state="readonly", width=20)
		program.grid(row=0, column=1, sticky="w", padx=8)
		ttk.Label(frame, text="Workers (1–128)").grid(row=1, column=0, sticky="w")
		count = ttk.Spinbox(frame, from_=1, to=128, textvariable=self.count, width=8)
		count.grid(row=1, column=1, sticky="w", padx=8)
		apply_count = ttk.Button(frame, text="Apply worker count", command=self.apply_count)
		apply_count.grid(row=1, column=2, padx=8)
		edit_worker = ttk.Button(frame, text="Edit selected worker…", command=self.edit_worker)
		edit_worker.grid(row=0, column=2, padx=8)
		self.widgets.extend((program, count, apply_count, edit_worker))
		self.engine.trace_add("write", self.changed)
		self.count.trace_add("write", self.changed)
		self.set_enabled(False)

	def edit_options(self, key=None, group="Advanced"):
		if self.document is None or self.app.monitor.active or self.app.jobs.busy or self.app.quit_pending:
			return
		if self.options_window is not None and self.options_window.winfo_exists():
			self.options_window.lift()
			return
		window = self.options_window = tk.Toplevel(self.app.root)
		hardware = group == "Hardware"
		connection = group == "Connection"
		behavior = group == "Behavior"
		title = "Update and output preferences" if behavior else "Connection settings" if connection else "Hardware and resource settings" if hardware else "Advanced assignment settings"
		window.title(title)
		window.transient(self.app.root)
		window.geometry("740x600")
		outer = ttk.Frame(window, padding=12)
		outer.pack(fill="both", expand=True)
		intro = ("Blank retains INI inheritance or the backend's automatic CPU detection/defaults.\nThese values are reported to PrimeNet during registration or computer updates. They do not configure your computation program." if hardware else "Blank uses the backend default. True/False explicitly overrides it.\nThese settings can change assignment selection or rewrite assignments during monitoring.")
		if connection:
			intro = "Blank uses INI/backend defaults. Proxy settings apply when monitoring communicates with servers.\nUse Manage SMTP and proxy passwords to change passwords."
		if behavior:
			intro = "Blank uses INI/backend defaults. These preferences are saved locally; no update check runs during Save."
		ttk.Label(outer, text=intro, wraplength=680).pack(anchor="w", pady=(0, 8))
		body = ttk.Frame(outer)
		body.pack(fill="both", expand=True)
		canvas = tk.Canvas(body, highlightthickness=0)
		scrollbar = ttk.Scrollbar(body, orient="vertical", command=canvas.yview)
		canvas.configure(yscrollcommand=scrollbar.set)
		scrollbar.pack(side="right", fill="y")
		canvas.pack(side="left", fill="both", expand=True)
		frame = ttk.Frame(canvas)
		item = canvas.create_window(0, 0, window=frame, anchor="nw")
		frame.columnconfigure(1, weight=1)
		frame.bind("<Configure>", lambda _: canvas.configure(scrollregion=canvas.bbox("all")))
		canvas.bind("<Configure>", lambda event: canvas.itemconfigure(item, width=event.width))
		self.options_values = {}
		controls = {}
		for row, field in enumerate(field for field in FIELDS if (field.dialog or field.tab) == group):
			variable = tk.StringVar(value=self.values[field.key].get())
			self.options_values[field.key] = variable
			ttk.Label(frame, text=field.label).grid(row=row, column=0, sticky="w", padx=(0, 8), pady=5)
			choices = ("", "True", "False") if field.kind == "boolean" else field.choices
			widget = ttk.Combobox(frame, textvariable=variable, values=choices, state="readonly") if choices else ttk.Entry(frame, textvariable=variable)
			widget.grid(row=row, column=1, sticky="ew", pady=5)
			controls[field.key] = widget
			# Keyboard traversal keeps the focused field reachable on short displays.
			widget.bind("<FocusIn>", lambda event: canvas.yview_moveto(max(0, (event.widget.winfo_y() - 20) / max(1, frame.winfo_height()))))
		help_text = ("Total physical memory (memory) and maximum stage 2 memory (Memory) are separate settings. Maximum memory cannot exceed total memory.\nUse Detect GPUs to review local devices. Blank hardware overrides use CPU detection/defaults." if hardware else "P−1 retry threshold is used with force P−1. LL↔PRP conversions are mutually exclusive.\nSave settings validates all options with AutoPrimeNet before writing.")
		if connection:
			help_text = "SOCKS proxies require the optional PySocks package. Encryption True is strict; blank uses opportunistic encryption in the CLI.\nThe GUI always requires encryption for new passwords. Existing encrypted passwords require encryption enabled or inherited."
		elif behavior:
			help_text = "Update checks occur during normal backend monitoring. Native console-color preferences do not change the GUI or plain backend log."
		elif not hardware:
			help_text += "\nWithholding ≥100M-digit prime results requires another notification method, as in the CLI."
		ttk.Label(outer, text=help_text, wraplength=680).pack(anchor="w", pady=8)
		buttons = ttk.Frame(outer)
		buttons.pack(fill="x")
		ttk.Button(buttons, text="Apply to form", command=self.apply_options).pack(side="left")
		if hardware:
			ttk.Button(buttons, text="Detect GPUs…", command=self.discover_gpus).pack(side="left", padx=8)
		ttk.Button(buttons, text="Cancel", command=window.destroy).pack(side="right")
		window.bind("<Escape>", lambda _: window.destroy())
		window.grab_set()
		if key in controls:
			window.update_idletasks()
			controls[key].focus_set()
		return window

	def discover_gpus(self):
		if self.app.monitor.active or self.app.jobs.busy or self.app.quit_pending:
			return
		self.gpu_target = self.options_window
		if self.app.jobs.submit("discover_gpus", backend_request, "discover_gpus"):
			self.app.set_busy(True)
			self.app.status.set("Detecting local GPUs; no server contacted…")

	def complete_gpus(self, value, error):
		target = self.gpu_target
		self.gpu_target = None
		if target is None or not target.winfo_exists() or target is not self.options_window or self.app.quit_pending:
			return
		if error:
			messagebox.showerror("GPU discovery", "Local GPU discovery failed. Check GPU drivers or enter hardware manually.", parent=target)
			return
		devices = value["devices"]
		self.app.status.set("GPU discovery finished; settings remain unsaved.")
		if not devices:
			messagebox.showinfo("GPU discovery", "No supported GPUs were detected. You can enter hardware manually.", parent=target)
			return
		window = tk.Toplevel(target)
		window.title("Select GPU to report to PrimeNet")
		window.transient(target)
		frame = ttk.Frame(window, padding=12)
		frame.pack(fill="both", expand=True)
		ttk.Label(frame, text="Choose the GPU used by your computation program. Duplicate devices may appear.\nThis changes reported hardware only; it does not select an engine device.").pack(anchor="w")
		choice = tk.StringVar(value="")
		selector = ttk.Combobox(frame, textvariable=choice, state="readonly", width=65,
			values=[f"{i + 1}. {device['name']} ({device['source']})" for i, device in enumerate(devices)])
		selector.pack(fill="x", pady=8)
		details = tk.StringVar(value="Select a device to review its settings.")
		ttk.Label(frame, textvariable=details, wraplength=620).pack(anchor="w", pady=8)
		def review(_event=None):
			index = selector.current()
			if index >= 0:
				details.set("\n".join(f"{key}: {text}" for key, text in devices[index]["settings"].items()))
		selector.bind("<<ComboboxSelected>>", review)
		def apply():
			index = selector.current()
			if index < 0 or self.app.jobs.busy or self.app.monitor.active:
				return
			for key, text in devices[index]["settings"].items():
				self.options_values[key].set(text)
			window.destroy()
			target.grab_set()
		buttons = ttk.Frame(frame)
		buttons.pack(fill="x", pady=8)
		ttk.Button(buttons, text="Use in hardware dialog", command=apply).pack(side="left")
		def cancel():
			window.destroy()
			target.grab_set()
		ttk.Button(buttons, text="Cancel", command=cancel).pack(side="right")
		window.protocol("WM_DELETE_WINDOW", cancel)
		window.bind("<Escape>", lambda _: cancel())
		window.grab_set()

	def apply_options(self):
		if self.app.monitor.active or self.app.jobs.busy or self.app.quit_pending:
			messagebox.showerror("Configuration settings", "Wait for local operations and monitoring to stop before applying changes.", parent=self.options_window)
			return False
		values = {key: variable.get() for key, variable in self.values.items()}
		values.update({key: variable.get() for key, variable in self.options_values.items()})
		try:
			validate_fields(values)
			if values["convert_ll_to_prp"] == values["convert_prp_to_ll"] == "True":
				raise ValueError("Choose only one LL/PRP conversion direction.")
		except ValueError as error:
			messagebox.showerror("Configuration settings", str(error), parent=self.options_window)
			return False
		for key, variable in self.options_values.items():
			if self.values[key].get() != variable.get():
				self.values[key].set(variable.get())
		self.options_window.destroy()
		return True

	def edit_passwords(self):
		if self.document is None or self.app.monitor.active or self.app.jobs.busy or self.app.quit_pending:
			return
		if self.password_window is not None and self.password_window.winfo_exists():
			self.password_window.lift()
			return
		window = self.password_window = tk.Toplevel(self.app.root)
		window.title("Manage passwords")
		window.transient(self.app.root)
		frame = ttk.Frame(window, padding=14)
		frame.pack(fill="both", expand=True)
		ttk.Label(frame, text="Saved passwords are never loaded into these fields. Replacement passwords are encrypted when you Save settings.\nKeep retains pending edits; Use saved discards a pending edit. Remove deletes the saved password on Save.", wraplength=680).grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 12))
		self.password_modes, self.password_values = {}, {}
		for row, (key, label, section, option) in enumerate((("email", "SMTP password", "Email", "password"), ("proxy", "Proxy password", "PrimeNet", "ProxyPass")), 1):
			pending = "replacement pending" if self.credentials.get(key) is not None else "removal pending"
			stored = "saved" if any(self.document.config.has_option(section, name) for name in (option, "encrypted_" + option)) else "not saved"
			ttk.Label(frame, text=label + " (" + (pending if key in self.credentials else stored) + ")").grid(row=row, column=0, sticky="w", padx=(0, 10))
			mode = self.password_modes[key] = tk.StringVar(value="Keep")
			value = self.password_values[key] = tk.StringVar()
			ttk.Combobox(frame, textvariable=mode, values=("Keep", "Replace", "Remove", "Use saved"), state="readonly", width=12).grid(row=row, column=1, padx=6, pady=8)
			entry = ttk.Entry(frame, textvariable=value, show="*", width=32, state="disabled")
			entry.grid(row=row, column=2, pady=8)
			mode.trace_add("write", lambda *_, mode=mode, entry=entry: entry.configure(state="normal" if mode.get() == "Replace" else "disabled"))

		def close():
			for value in self.password_values.values():
				value.set("")
			window.destroy()

		self.close_passwords = close
		ttk.Button(frame, text="Apply to form", command=self.apply_passwords).grid(row=3, column=0, sticky="w", pady=12)
		ttk.Button(frame, text="Cancel", command=close).grid(row=3, column=2, sticky="e", pady=12)
		window.protocol("WM_DELETE_WINDOW", close)
		window.bind("<Escape>", lambda _: close())
		window.grab_set()
		return window

	def apply_passwords(self):
		if self.app.monitor.active or self.app.jobs.busy or self.app.quit_pending:
			messagebox.showerror("Passwords", "Stop monitoring and wait for local operations before applying changes.", parent=self.password_window)
			return False
		changes = dict(self.credentials)
		for key, mode in self.password_modes.items():
			if mode.get() == "Replace":
				secret = self.password_values[key].get()
				if not secret or len(secret) > 4096 or any(char in secret for char in "\r\n\x00"):
					messagebox.showerror("Passwords", "Enter a password of 1–4096 characters without line breaks or NUL.", parent=self.password_window)
					return False
				changes[key] = secret
			elif mode.get() == "Remove":
				changes[key] = None
			elif mode.get() == "Use saved":
				changes.pop(key, None)
		if changes != self.credentials:
			self.credentials = changes
			self.changed()
		self.close_passwords()
		return True

	def changed(self, *_):
		if not self.loading and self.document is not None:
			self.dirty = True
			self.app.status.set("Unsaved configuration changes — monitoring and server operations remain unavailable")

	def set_enabled(self, enabled):
		for widget in self.widgets:
			widget.state(["!disabled"] if enabled else ["disabled"])

	def load(self, document):
		self.loading = True
		try:
			self.document = document
			self.credentials.clear()
			for key, value in document.values().items():
				field = next(field for field in FIELDS if field.key == key)
				if field.kind == "boolean" and value:
					value = str(document.config.getboolean(field.section, field.ini_key))
				self.values[key].set(value)
			config = document.config
			engines = [name for name in ENGINES if config.getboolean("PrimeNet", name, fallback=False)]
			self.engine.set(engines[0] if engines else "")
			count = config.getint("PrimeNet", "NumWorkers", fallback=1)
			self.count.set(str(count))
			self.worker_values = []
			for index in range(count):
				section = "Worker #{}".format(index + 1) if count > 1 else "PrimeNet"
				self.worker_values.append({
					"directory": config.get(section, "directory", fallback=""),
					"preference": config.get(section, "WorkPreference", fallback=""),
				})
			self.dirty = False
			self.set_enabled(True)
		finally:
			self.loading = False

	def apply_count(self):
		try:
			count = int(self.count.get())
			if not 1 <= count <= 128:
				raise ValueError
		except ValueError:
			messagebox.showerror("Workers", "Enter a worker count between 1 and 128.", parent=self.app.root)
			return False
		if count < len(self.worker_values) and not messagebox.askyesno("Reduce workers", "Remove these workers from the active GUI configuration? Their files and unknown INI sections will be preserved.", parent=self.app.root):
			return False
		self.worker_values = (self.worker_values + [{"directory": "", "preference": ""} for _ in range(count)])[:count]
		self.changed()
		self.show_workers()
		return True

	def show_workers(self):
		table = self.app.workers
		table.delete(*table.get_children())
		for index, worker in enumerate(self.worker_values):
			table.insert("", "end", iid=str(index), values=(index + 1, worker["directory"] or "Working directory", worker["preference"] or "Program default", "Unsaved configuration" if self.dirty else "Configured"))

	def edit_worker(self):
		selected = self.app.workers.selection()
		if not selected:
			messagebox.showinfo("Workers", "Select a worker in the table first.", parent=self.app.root)
			return
		index = self.app.workers.index(selected[0])
		if index >= len(self.worker_values):
			return
		window = tk.Toplevel(self.app.root)
		window.title("Configure worker #{}".format(index + 1))
		window.transient(self.app.root)
		frame = ttk.Frame(window, padding=12)
		frame.pack(fill="both", expand=True)
		directory = tk.StringVar(value=self.worker_values[index]["directory"])
		preference = tk.StringVar(value=self.worker_values[index]["preference"])
		ttk.Label(frame, text="Directory (blank: working directory; PRPLL requires blank)").grid(row=0, column=0, columnspan=2, sticky="w")
		ttk.Entry(frame, textvariable=directory, width=55).grid(row=1, column=0, sticky="ew", pady=6)

		def browse():
			chosen = filedialog.askdirectory(parent=window)
			if chosen:
				directory.set(chosen)

		ttk.Button(frame, text="Browse…", command=browse).grid(row=1, column=1, padx=6)
		ttk.Label(frame, text="Work preference code (blank: program default)").grid(row=2, column=0, sticky="w")
		ttk.Combobox(frame, textvariable=preference, values=("", "2", "4", "5", "8", "12", "100", "101", "102", "104", "106", "150", "151", "152", "153", "154", "155", "160", "161"), width=15).grid(row=3, column=0, sticky="w", pady=6)
		ttk.Label(frame, text="Backend validation checks which codes this computation program accepts.", wraplength=460).grid(row=4, column=0, columnspan=2, sticky="w")

		def accept():
			self.worker_values[index] = {"directory": directory.get().strip(), "preference": preference.get().strip()}
			self.changed()
			self.show_workers()
			window.destroy()

		ttk.Button(frame, text="Apply to form", command=accept).grid(row=5, column=0, pady=10, sticky="w")
		ttk.Button(frame, text="Cancel", command=window.destroy).grid(row=5, column=1, pady=10)
		window.grab_set()

	def collect(self):
		if self.document is None:
			raise ValueError("Load a working directory before saving.")
		try:
			count = int(self.count.get())
		except ValueError as error:
			raise ValueError("Enter a valid worker count and apply it before saving.") from error
		if count != len(self.worker_values):
			raise ValueError("Apply the worker count before saving.")
		return ({key: value.get() for key, value in self.values.items()}, self.engine.get(), [dict(worker) for worker in self.worker_values], dict(self.credentials))
