"""Independent, asynchronous Progress tab for running computation engines.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from datetime import datetime
from functools import partial
import time
import tkinter as tk
from tkinter import ttk

from gui_controller import BackgroundJobs, backend_request
from gui_progress import format_duration


class ProgressView:
	def __init__(self, app):
		self.app = app
		self.jobs = BackgroundJobs()
		self.configured = None
		self.due = 0
		self.records = {}
		self.observed = {}
		frame = app.tabs["Progress"]
		ttk.Label(frame, text="Running computation programs", font=("TkDefaultFont", 14, "bold")).pack(anchor="w")
		ttk.Label(frame, text="Automatically discovers local processes and reads their saved progress. Updates every 15 seconds while this tab is open.\nCheckpoints can lag computation; data older than 15 minutes is marked stale, which does not establish a stall.\nSelect a row for its full assignment and file paths. No PrimeNet connection or monitoring is required.", wraplength=940, justify="left").pack(anchor="w", pady=8)
		controls = ttk.Frame(frame)
		controls.pack(fill="x")
		self.button = ttk.Button(controls, text="Refresh progress", command=self.refresh)
		self.button.pack(side="left")
		self.automatic = tk.BooleanVar(value=True)
		ttk.Checkbutton(controls, text="Automatic refresh", variable=self.automatic).pack(side="left", padx=12)
		self.status = tk.StringVar(value="Open this tab to discover running computation programs.")
		ttk.Label(frame, textvariable=self.status, wraplength=940).pack(anchor="w", pady=6)
		area = ttk.Frame(frame)
		area.pack(fill="both", expand=True)
		columns = ("Program", "PID(s)", "Worker", "Exponent", "Stage", "Progress", "Speed", "Remaining", "Completion estimate", "Last update", "State", "Queued work", "FFT")
		self.table = ttk.Treeview(area, columns=columns, show="headings", height=8)
		for column in columns:
			self.table.heading(column, text=column)
			self.table.column(column, width=135 if column in {"Completion estimate", "Last update", "State"} else 110, minwidth=65)
		xscroll = ttk.Scrollbar(area, orient="horizontal", command=self.table.xview)
		yscroll = ttk.Scrollbar(area, orient="vertical", command=self.table.yview)
		self.table.configure(xscrollcommand=xscroll.set, yscrollcommand=yscroll.set)
		self.table.grid(row=0, column=0, sticky="nsew")
		yscroll.grid(row=0, column=1, sticky="ns")
		xscroll.grid(row=1, column=0, sticky="ew")
		area.rowconfigure(0, weight=1)
		area.columnconfigure(0, weight=1)
		self.details = tk.StringVar(value="No row selected.")
		ttk.Label(frame, textvariable=self.details, wraplength=940, justify="left").pack(anchor="w", pady=8)
		self.table.bind("<<TreeviewSelect>>", self.select)

	def refresh(self):
		if self.jobs.busy or self.app.closed or self.app.quit_pending:
			return
		if self.jobs.submit("progress", partial(backend_request, "progress", configured=self.configured)):
			self.button.configure(state="disabled")
			self.status.set("Discovering processes and reading progress…")

	def tick(self):
		result = self.jobs.take()
		if result:
			_, value, error = result
			self.button.configure(state="normal")
			self.due = time.monotonic() + 15
			if error:
				self.table.delete(*self.table.get_children())
				self.records.clear()
				self.details.set("No current snapshot available.")
				self.status.set("Progress scan failed or timed out. Check dependencies and permissions, then refresh.")
			else:
				self.display(value)
		if self.automatic.get() and time.monotonic() >= self.due and self.app.notebook.select() == str(self.app.tabs["Progress"]):
			self.refresh()

	def display(self, snapshot):
		selected = self.table.selection()
		prior = self.records.get(selected[0]) if selected else None
		self.table.delete(*self.table.get_children())
		self.records.clear()
		self.details.set("Select a row for assignment and directory details.")
		self.status.set(snapshot["notice"] + (" No supported running programs found." if not snapshot["rows"] and snapshot.get("discovery_available", True) else ""))
		observed = {}
		for row in snapshot["rows"]:
			key = tuple(row.get(field) for field in ("engine", "pids", "directory", "worker", "exponent", "stage"))
			old = self.observed.get(key)
			observed[key] = row.get("iteration")
			state = row["state"]
			if old is not None and row.get("iteration", 0) > old:
				state = "Progress advanced since previous scan"
			remaining, updated = row.get("remaining"), row.get("updated")
			# Anchor the estimate to the saved-data time: rereading an unchanged
			# checkpoint must not move its estimated completion forward each scan.
			try:
				completion = datetime.fromtimestamp(row["completion"]).strftime("%Y-%m-%d %H:%M:%S") if row.get("completion") is not None else "Unavailable"
			except (OverflowError, OSError, ValueError):
				completion = "Unavailable"
			values = (
				row["engine"], row["pids"], row["worker"], row.get("exponent", "—"), row.get("stage", "Unavailable"),
				f'{row["percent"]:.2f}%' if row.get("percent") is not None else "Unavailable",
				(f'{row["speed"]:.3f} ms/GHz-day' if row.get("stage") == "TF" else f'{row["speed"]:.3f} ms/iteration') if row.get("speed") is not None else "Unavailable",
				format_duration(remaining), completion,
				datetime.fromtimestamp(updated).strftime("%Y-%m-%d %H:%M:%S") if updated else "Unavailable",
				state, row.get("queue", "—"), row.get("fft") or "Unavailable",
			)
			item = self.table.insert("", "end", values=values)
			self.records[item] = row
			if prior and all(row.get(field) == prior.get(field) for field in ("engine", "directory", "worker", "exponent")):
				self.table.selection_set(item)
				self.select()
		self.observed = observed

	def select(self, _event=None):
		selected = self.table.selection()
		if selected and selected[0] in self.records:
			row = self.records[selected[0]]
			self.details.set(f'Directory: {row["directory"]}\nWork file: {row.get("work_file", "Unavailable")}\nAssignment: {row.get("assignment", "Unavailable")}')

	def close(self):
		self.jobs.close()
