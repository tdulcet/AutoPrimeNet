"""Graphical configuration fields and worker editing.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from gui_config import ENGINES
from gui_options import FIELDS


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
		for tab in dict.fromkeys(field.tab for field in FIELDS):
			frame = ttk.LabelFrame(app.tabs[tab], text="Local configuration", padding=8)
			frame.pack(fill="x", pady=(0, 8))
			frame.columnconfigure(1, weight=1)
			for row, field in enumerate(field for field in FIELDS if field.tab == tab):
				variable = tk.StringVar(value=field.default)
				variable.trace_add("write", self.changed)
				self.values[field.key] = variable
				ttk.Label(frame, text=field.label).grid(row=row, column=0, sticky="w", padx=(0, 8), pady=2)
				if field.kind == "boolean":
					widget = ttk.Combobox(frame, textvariable=variable, values=("", "True", "False"), state="readonly", width=12)
				else:
					widget = ttk.Entry(frame, textvariable=variable)
				widget.grid(row=row, column=1, sticky="ew", pady=2)
				self.widgets.append(widget)
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
			for key, value in document.values().items():
				field = next(field for field in FIELDS if field.key == key)
				if field.kind == "boolean" and value:
					value = str(document.config.getboolean("PrimeNet", key))
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
		return ({key: value.get() for key, value in self.values.items()}, self.engine.get(), [dict(worker) for worker in self.worker_values])
