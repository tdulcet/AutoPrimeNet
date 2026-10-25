"""Graphical batch editing and offline preview for exponent registration.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import tkinter as tk
from tkinter import messagebox, ttk

from gui_controller import backend_request
from gui_registration_plan import DEFAULT_ENTRY, WORK_TYPES, validate_shape


LABELS = {
	"exponent": "Exponent", "sieve_depth": "TF bits / start bits", "factor_to": "TF end bits",
	"pminus1ed": "Previously P−1 factored", "tests_saved": "Primality tests saved",
	"B1": "P−1 / ECM B1", "B2": "P−1 / ECM B2", "curves": "ECM curves",
	"prp_base": "PRP double-check base", "prp_residue_type": "PRP residue type (1–5)",
	"known_factors": "Known prime factors (comma-separated)",
}


def request_preview(document, parameters):
	return backend_request("preview_registration", text=document.text, directory=str(document.directory), config_name=document.path.name, parameters=parameters)


class RegistrationForm:
	def __init__(self, app):
		self.app = app
		self.window = None
		self.entries = []
		self.preview = None
		self.widgets = []

	@property
	def dirty(self):
		return self.window is not None and self.window.winfo_exists() and bool(self.entries)

	def open(self):
		if self.app.jobs.busy or self.app.monitor.active or self.app.quit_pending or self.app.editor.document is None:
			return
		if self.window is not None and self.window.winfo_exists():
			self.window.lift()
			return
		self.document = self.app.editor.document
		self.entries, self.preview, self.widgets = [], None, []
		window = self.window = tk.Toplevel(self.app.root)
		window.title("Register exponent batch")
		window.transient(self.app.root)
		window.geometry("{}x{}".format(min(940, window.winfo_screenwidth() - 80), min(760, window.winfo_screenheight() - 100)))
		window.minsize(740, 620)
		outer = ttk.Frame(window, padding=12)
		outer.pack(fill="both", expand=True)
		ttk.Label(outer, text="Advanced: choose explicit values, queue rows, then preview offline. Registration appends work and contacts PrimeNet only after typed confirmation.\nChoose work types appropriate to your computation engine. No mersenne.ca metadata lookup is performed; preview is not server acceptance.", wraplength=890).pack(anchor="w")
		form = ttk.Frame(outer)
		form.pack(fill="x", pady=8)
		self.worker = tk.StringVar(value="1")
		self.worker.trace_add("write", lambda *_: self.invalidate())
		ttk.Label(form, text="Worker").grid(row=0, column=0, sticky="w")
		widget = ttk.Spinbox(form, from_=1, to=self.document.config.getint("PrimeNet", "NumWorkers", fallback=1), textvariable=self.worker, width=8)
		widget.grid(row=0, column=1, sticky="w", pady=3)
		self.widgets.append(widget)
		self.values = {key: tk.StringVar(value=", ".join(map(str, value)) if isinstance(value, list) else str(value)) for key, value in DEFAULT_ENTRY.items()}
		ttk.Label(form, text="Work type").grid(row=0, column=2, sticky="w", padx=(12, 8))
		self.work_type = tk.StringVar(value="150 — " + WORK_TYPES[150])
		widget = ttk.Combobox(form, textvariable=self.work_type, values=tuple("{} — {}".format(key, value) for key, value in WORK_TYPES.items()), state="readonly", width=25)
		widget.grid(row=0, column=3, sticky="ew")
		self.widgets.append(widget)
		self.controls = {}
		for index, (key, label) in enumerate(LABELS.items()):
			row, column = 1 + index // 2, 2 * (index % 2)
			ttk.Label(form, text=label).grid(row=row, column=column, sticky="w", padx=(0 if column == 0 else 12, 8), pady=3)
			if key == "pminus1ed":
				widget = ttk.Combobox(form, textvariable=self.values[key], values=("False", "True"), state="readonly")
			else:
				widget = ttk.Entry(form, textvariable=self.values[key])
			widget.grid(row=row, column=column + 1, sticky="ew", pady=3)
			self.controls[key] = widget
			self.widgets.append(widget)
		form.columnconfigure(1, weight=1)
		form.columnconfigure(3, weight=1)
		self.work_type.trace_add("write", lambda *_: self.set_busy(False))
		self.values["prp_residue_type"].trace_add("write", lambda *_: self.set_busy(False))
		buttons = ttk.Frame(outer)
		buttons.pack(fill="x")
		for label, command in (("Add row", self.add), ("Replace selected row", self.replace), ("Remove selected row", self.remove)):
			button = ttk.Button(buttons, text=label, command=command)
			button.pack(side="left", padx=(0, 8), pady=4)
			self.widgets.append(button)
		self.table = ttk.Treeview(outer, columns=("type", "exponent", "factors"), show="headings", height=5)
		for key, label in (("type", "Work type"), ("exponent", "Exponent"), ("factors", "Known factors")):
			self.table.heading(key, text=label)
		self.table.pack(fill="both", expand=True, pady=6)
		self.table.bind("<<TreeviewSelect>>", self.select)
		preview_frame = ttk.Frame(outer)
		preview_frame.pack(fill="both", expand=True)
		self.output = tk.Text(preview_frame, height=5, wrap="none", state="disabled")
		horizontal = ttk.Scrollbar(preview_frame, orient="horizontal", command=self.output.xview)
		vertical = ttk.Scrollbar(preview_frame, orient="vertical", command=self.output.yview)
		self.output.configure(xscrollcommand=horizontal.set, yscrollcommand=vertical.set)
		horizontal.pack(side="bottom", fill="x")
		vertical.pack(side="right", fill="y")
		self.output.pack(fill="both", expand=True)
		self.status = tk.StringVar(value="Queue up to 100 entries for one worker. No work files have been changed.")
		ttk.Label(outer, textvariable=self.status, wraplength=880).pack(anchor="w", pady=6)
		bottom = ttk.Frame(outer)
		bottom.pack(fill="x")
		self.preview_button = ttk.Button(bottom, text="Validate and preview offline", command=self.request_preview)
		self.preview_button.pack(side="left")
		self.widgets.append(self.preview_button)
		self.launch_button = ttk.Button(bottom, text="Register validated batch…", command=self.launch, state="disabled")
		self.launch_button.pack(side="left", padx=8)
		ttk.Button(bottom, text="Cancel", command=self.close).pack(side="right")
		window.protocol("WM_DELETE_WINDOW", self.close)
		window.bind("<Escape>", lambda _: self.close())
		window.grab_set()
		self.set_busy(False)
		return window

	def enabled_fields(self):
		kind = int(self.work_type.get().split(" — ")[0])
		try:
			residue = int(self.values["prp_residue_type"].get())
		except ValueError:
			residue = None
		fields = {"exponent"}
		if kind != 5:
			fields.add("sieve_depth")
		if kind == 2:
			fields.add("factor_to")
		if kind in {100, 101}:
			fields.add("pminus1ed")
		if kind in {4, 150, 151}:
			fields.add("tests_saved")
		gpuowl = self.document.config.getboolean("PrimeNet", "gpuowl", fallback=False)
		if kind in {3, 5} or gpuowl and kind in {4, 150, 151}:
			fields.update(("B1", "B2"))
		if kind == 5:
			fields.add("curves")
		if kind == 151:
			fields.update(("prp_base", "prp_residue_type"))
		if kind in {2, 3, 4, 5, 150} or kind == 151 and residue == 5:
			fields.add("known_factors")
		return fields

	def set_busy(self, busy):
		if self.window is None or not self.window.winfo_exists():
			return
		busy = busy or self.app.jobs.busy or self.app.monitor.active or self.app.quit_pending
		for widget in self.widgets:
			widget.state(["disabled"] if busy else ["!disabled"])
		for key, widget in self.controls.items():
			widget.state(["!disabled"] if not busy and key in self.enabled_fields() else ["disabled"])
		self.launch_button.state(["!disabled"] if self.preview is not None and not busy else ["disabled"])

	def collect_entry(self):
		entry = dict(DEFAULT_ENTRY, work_type=int(self.work_type.get().split(" — ")[0]))
		for key in self.enabled_fields():
			value = self.values[key].get().strip()
			if key == "known_factors":
				entry[key] = [int(item.strip()) for item in value.split(",")] if value else []
			elif key == "pminus1ed":
				entry[key] = value == "True"
			else:
				entry[key] = float(value) if key in {"sieve_depth", "tests_saved"} else int(value)
		return entry

	def mutate(self, replace=False):
		if self.app.jobs.busy or self.app.monitor.active:
			return
		try:
			entries = list(self.entries)
			entry = self.collect_entry()
			if replace:
				selected = self.table.selection()
				if not selected:
					raise ValueError("Select a queued row to replace.")
				entries[self.table.index(selected[0])] = entry
			else:
				entries.append(entry)
			self.entries = validate_shape({"worker": int(self.worker.get()), "entries": entries})["entries"]
		except ValueError as error:
			messagebox.showerror("Exponent batch", str(error), parent=self.window)
			return False
		self.invalidate()
		self.show_rows()
		return True

	def add(self):
		return self.mutate()

	def replace(self):
		return self.mutate(replace=True)

	def remove(self):
		if self.app.jobs.busy or self.app.monitor.active:
			return
		selected = self.table.selection()
		if selected:
			self.entries.pop(self.table.index(selected[0]))
			self.invalidate()
			self.show_rows()

	def select(self, _event=None):
		selected = self.table.selection()
		if selected:
			entry = self.entries[self.table.index(selected[0])]
			self.work_type.set("{} — {}".format(entry["work_type"], WORK_TYPES[entry["work_type"]]))
			for key, value in entry.items():
				self.values[key].set(", ".join(map(str, value)) if isinstance(value, list) else str(value))

	def show_rows(self):
		self.table.delete(*self.table.get_children())
		for row in self.entries:
			self.table.insert("", "end", values=(WORK_TYPES[row["work_type"]], row["exponent"], ", ".join(map(str, row["known_factors"]))))

	def invalidate(self):
		self.preview = None
		if hasattr(self, "launch_button") and self.window is not None and self.window.winfo_exists():
			self.launch_button.state(["disabled"])
			self.output.configure(state="normal")
			self.output.delete("1.0", "end")
			self.output.configure(state="disabled")
			self.status.set("Batch changed; validate and preview before registering.")

	def request_preview(self):
		if self.app.jobs.busy or self.app.monitor.active:
			return
		if self.document is not self.app.editor.document:
			self.document = self.app.editor.document
			self.invalidate()
		try:
			plan = validate_shape({"worker": int(self.worker.get()), "entries": self.entries})
		except ValueError as error:
			messagebox.showerror("Exponent batch", str(error), parent=self.window)
			return
		if self.app.jobs.submit("registration_preview", request_preview, self.document, plan):
			self.app.set_busy(True)
			self.status.set("Validating with the original backend offline…")

	def complete_preview(self, value, error):
		if self.window is None or not self.window.winfo_exists():
			return
		if error:
			self.preview = None
			self.status.set(str(error))
		else:
			self.preview = value
			self.output.configure(state="normal")
			self.output.delete("1.0", "end")
			self.output.insert("end", "\n".join(value["lines"]))
			self.output.configure(state="disabled")
			self.status.set("Validated offline: {} work lines. No files written; server acceptance unverified.".format(len(value["lines"])))
		self.set_busy(False)

	def launch(self):
		if self.preview is None or self.app.jobs.busy or self.app.monitor.active:
			return
		if self.app.editor.document is not self.document:
			self.document = self.app.editor.document
			self.invalidate()
			self.status.set("Configuration changed; validate this batch again before registering.")
			return
		if self.app.run_operation("register_exponents", parameters=self.preview["plan"]):
			self.close()
		else:
			self.window.grab_set()

	def close(self):
		if self.window is not None and self.window.winfo_exists():
			self.window.destroy()
		self.window, self.entries, self.preview = None, [], None
