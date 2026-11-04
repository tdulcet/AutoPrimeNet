"""Read-only process discovery and native computation progress snapshots.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from configparser import ConfigParser
from datetime import datetime, timedelta
import logging
import math
import os
from pathlib import Path
import re
import stat
import sys
import time
from types import SimpleNamespace


ENGINES = ("Mlucas", "GpuOwl", "PRPLL", "PrMers", "CUDALucas", "mfaktc", "mfakto", "PrimePath")
REPORT_ONLY = ("Prime95", "MPrime", "CUDAPm1", "cofact", "gvtf", "Mp_p-1_gpu")
WORK_TYPES = {2: "TF", 3: "P-1", 4: "P-1", 5: "ECM", 6: "P+1", 100: "LL", 101: "LL double-check", 150: "PRP", 200: "Certification"}
MAX_PROCESSES = 128
MAX_ASSIGNMENTS = 1000
MAX_FILE_BYTES = 2 * 1024 * 1024
STALE_SECONDS = 900


def identify_engine(name):
	"""Match executable basenames, including common version/architecture suffixes."""
	name = Path(name or "").name.lower().removesuffix(".exe")
	for engine in (*ENGINES, *REPORT_ONLY):
		if re.fullmatch(re.escape(engine.lower()) + r"(?:[-_.](?:v?\d.*|avx.*|sse.*|cuda.*|opencl.*|ntt.*|x86.*|x64|arm.*))?", name):
			return engine
	return None


def discover_processes(psutil):
	processes, denied, truncated = [], 0, False
	for process in psutil.process_iter():
		try:
			engine = identify_engine(process.name())
			if engine is None:
				continue
			if len(processes) >= MAX_PROCESSES:
				truncated = True
				break
			created = process.create_time()
			try:
				directory = process.cwd()
			except (psutil.AccessDenied, NotImplementedError):
				directory = None
			processes.append({"engine": engine, "pid": process.pid, "created": created, "directory": directory})
		except psutil.AccessDenied:
			denied += 1
		except (psutil.NoSuchProcess, psutil.ZombieProcess):
			continue
	return processes, denied, truncated


class ReadTracker:
	"""Record only filenames opened by the native progress reader, never contents."""
	def __init__(self):
		self.paths = None

	def audit(self, event, args):
		if event == "open" and self.paths is not None and isinstance(args[0], (str, bytes, os.PathLike)):
			if len(self.paths) < 512:
				self.paths.add(os.fsdecode(args[0]))


def _workfiles(process, configured):
	directory = Path(process["directory"])
	if configured and process["engine"].casefold() == configured["engine"].casefold():
		workers = configured["workers"]
		if directory.resolve() != Path(configured["directory"]).resolve():
			workers = [worker for worker in workers if Path(worker["work_file"]).parent.resolve() == directory.resolve()]
		if workers:
			return [(str(worker["number"]), Path(worker["work_file"])) for worker in workers[:128]]
	if process["engine"] == "PRPLL":
		files = []
		for path in directory.glob("worktodo-*.txt"):
			match = re.fullmatch(r"worktodo-(\d+)\.txt", path.name)
			if match:
				files.append((str(int(match[1]) + 1), path))
			if len(files) >= 128:
				break
		return sorted(files, key=lambda item: int(item[0]))
	return [("1", next((directory / name for name in ("worktodo.txt", "worktodo.ini") if (directory / name).is_file()), directory / "worktodo.txt"))]


def _read_work(path):
	with os.fdopen(os.open(path, os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_BINARY", 0)), "rb") as stream:
		if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
			raise ValueError("Work file must be regular")
		data = stream.read(MAX_FILE_BYTES + 1)
	if len(data) > MAX_FILE_BYTES:
		raise ValueError("Work file exceeds 2 MiB")
	return data.decode("utf-8-sig").splitlines()


def _finite(value):
	return isinstance(value, (int, float)) and math.isfinite(value)


def _assignment_row(namespace, tracker, engine, directory, assignment, now):
	args = SimpleNamespace(**{name.lower(): name == engine for name in ENGINES}, debug=0, timeout=3600, cpu_hours=24)
	adapter = logging.LoggerAdapter(logging.getLogger("gui.progress"), {})
	tracker.paths = set()
	try:
		progress = namespace["get_progress_assignment"](args, adapter, str(directory), assignment)
		paths = tracker.paths
	finally:
		tracker.paths = None
	iteration, _, speed, curve, stage, fft = progress
	usable = bool(iteration or speed or stage or curve)
	modified = []
	if usable:
		for path in paths:
			# Lazy native imports can open library files as well as progress data.
			# Only inputs beneath this worker directory can date its progress.
			if not Path(path).absolute().is_relative_to(Path(directory).absolute()):
				continue
			try:
				modified.append(Path(path).stat().st_mtime)
			except OSError:
				pass
	updated = max(modified, default=None)
	total, remaining, _ = namespace["compute_progress"](ConfigParser(), args, assignment, speed, assignment.n, progress)
	percent = 100 * iteration / total if usable and _finite(total) and total > 0 else None
	if not _finite(percent) or not 0 <= percent <= 100:
		percent = None
	if not _finite(remaining) or remaining < 0 or not usable:
		remaining = None
	# A saved checkpoint is evidence of past work, not proof this PID is advancing it.
	return {
		"exponent": str(assignment.n), "iteration": iteration, "work_type": assignment.work_type, "assignment": namespace["output_assignment"](assignment),
		"stage": ("Stage " + str(stage) if stage is not None else WORK_TYPES.get(assignment.work_type, "Unknown")) + (f"; curve {curve}" if curve else ""),
		"percent": percent, "speed": speed if _finite(speed) and speed > 0 else None,
		"remaining": remaining, "updated": updated, "fft": str(fft) if fft else None,
		"state": "No saved progress / queued" if not usable else "Stale saved progress" if updated and now - updated > STALE_SECONDS else "Saved progress",
	}


def progress_snapshot(namespace, configured=None, psutil_module=None):
	if configured is not None:
		if not isinstance(configured, dict) or not isinstance(configured.get("directory"), str) or not isinstance(configured.get("engine"), str) or not isinstance(configured.get("workers"), list) or len(configured["workers"]) > 128:
			raise ValueError("Invalid configured progress sources")
		for worker in configured["workers"]:
			if not isinstance(worker, dict) or type(worker.get("number")) is not int or not isinstance(worker.get("work_file"), str):
				raise ValueError("Invalid configured progress worker")
	if psutil_module is None:
		try:
			import psutil as psutil_module
		except ImportError:
			return {"rows": [], "discovery_available": False, "notice": "Process discovery requires psutil. Install requirements-gui.txt in the GUI Python environment."}
	try:
		processes, denied, truncated = discover_processes(psutil_module)
	except (OSError, psutil_module.Error):
		return {"rows": [], "discovery_available": False, "notice": "Process listing unavailable: operating-system permissions prevent discovery."}
	tracker = ReadTracker()
	sys.addaudithook(tracker.audit)
	rows, now, seen, count = [], time.time(), set(), 0
	for process in processes:
		base = {"engine": process["engine"], "pids": str(process["pid"]), "directory": process["directory"] or "Unavailable", "worker": "—", "state": "Working directory unavailable (permissions/platform)"}
		if not process["directory"] or process["engine"] not in ENGINES:
			if process["engine"] not in ENGINES:
				base["state"] = "Detected; native progress reader unavailable for this program"
			rows.append(base)
			continue
		key = (process["engine"], process["directory"])
		if key in seen:
			continue
		seen.add(key)
		peers = [item for item in processes if (item["engine"], item["directory"]) == key]
		base["pids"] = ", ".join(str(item["pid"]) for item in peers)
		start = len(rows)
		try:
			files = _workfiles(process, configured)
			if not files:
				rows.append({**base, "state": "No indexed work files found"})
			for worker, path in files:
				worker_base = {**base, "worker": worker, "directory": str(path.parent), "work_file": str(path)}
				try:
					lines = _read_work(path)
					assignments = []
					for line in lines:
						if not line.strip() or line.lstrip().startswith(("#", ";")):
							continue
						assignment = namespace["parse_assignment"](logging.getLogger("gui.progress"), line)
						if assignment is not None:
							assignments.append(assignment)
						if len(assignments) >= MAX_ASSIGNMENTS - count:
							truncated = True
							break
					if not assignments:
						rows.append({**worker_base, "state": "No recognized assignments in work file"})
					previous = None
					cumulative = 0
					anchor = None
					for assignment in assignments:
						count += 1
						try:
							row = _assignment_row(namespace, tracker, process["engine"], path.parent, assignment, now)
						except (OSError, ValueError, ArithmeticError, EOFError, TypeError):
							row = {"exponent": str(assignment.n), "state": "Progress unreadable; retry after next checkpoint"}
						if row.get("speed"):
							previous = (assignment, row["speed"])
						elif previous and row.get("state") == "No saved progress / queued" and assignment.work_type == previous[0].work_type and assignment.work_type in {2, 100, 101, 150}:
							args = SimpleNamespace(cpu_hours=24)
							_, estimate, _ = namespace["compute_progress"](ConfigParser(), args, assignment, previous[1], previous[0].n, (0, None, None, None, None, None))
							if _finite(estimate) and estimate >= 0:
								row["remaining"] = estimate
								row["state"] = "Queued; estimated from worker speed"
						if anchor is None:
							anchor = row.get("updated")
						remaining = row.get("remaining")
						if remaining is None or cumulative is None:
							cumulative = None
						else:
							cumulative += remaining
						row["completion"] = anchor + cumulative if anchor is not None and cumulative is not None else None
						rows.append({**worker_base, **row, "queue": len(assignments)})
				except (OSError, ValueError, UnicodeError):
					rows.append({**worker_base, "state": "Work file unavailable, unreadable or too large"})
				if count >= MAX_ASSIGNMENTS:
					break
			# Recheck identity after file reads to avoid reporting an exited/reused PID.
			alive = []
			for peer in peers:
				try:
					if psutil_module.Process(peer["pid"]).create_time() == peer["created"]:
						alive.append(str(peer["pid"]))
				except (psutil_module.Error, OSError):
					pass
			for row in rows[start:]:
				row["pids"] = ", ".join(alive) or "Exited during scan"
		except (OSError, ValueError):
			rows.append({**base, "state": "Working directory unavailable"})
		if count >= MAX_ASSIGNMENTS:
			break
	notice = f"Scanned {len(processes)} matching processes at {datetime.fromtimestamp(now):%Y-%m-%d %H:%M:%S}."
	if denied:
		notice += f" {denied} processes could not be inspected (permissions)."
	if truncated:
		notice += " Display limit reached; some processes/assignments are omitted."
	return {"rows": rows, "notice": notice, "network_enabled": False, "files_written": False}


def format_duration(seconds):
	if seconds is None:
		return "Unavailable"
	try:
		return str(timedelta(seconds=int(seconds)))
	except (ValueError, OverflowError):
		return "Unavailable"
