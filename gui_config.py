"""Workspace discovery and validated local configuration persistence.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from configparser import ConfigParser, Error as ConfigError
from contextlib import contextmanager
import hashlib
import os
from pathlib import Path
import re
import shutil
import stat
import tempfile

from gui_controller import backend_request
from gui_options import FIELDS, validate_fields


MAX_FILE_BYTES = 2 * 1024 * 1024
ENGINES = ("mlucas", "gpuowl", "prpll", "prmers", "cudalucas", "mfaktc", "mfakto", "primepath")


class WorkspaceError(Exception):
	"""A readable workspace cannot be safely interpreted."""


def read_small_file(path):
	with path.open("rb") as stream:
		content = stream.read(MAX_FILE_BYTES + 1)
	if len(content) > MAX_FILE_BYTES:
		raise WorkspaceError("The selected file exceeds the 2 MiB preview limit.")
	return content.decode("utf-8-sig")


def workspace_snapshot(directory, config_name="prime.ini"):
	"""Read configured workers without saving, decrypting, locking or networking."""
	base = Path(directory).expanduser().resolve()
	if not base.is_dir():
		raise WorkspaceError("Select an existing working directory.")
	if not config_name or Path(config_name).name != config_name:
		raise WorkspaceError("Configuration name must be a filename, without a directory.")
	config = ConfigParser()
	config.optionxform = str
	config_path = base / config_name
	try:
		if config_path.exists():
			config.read_string(read_small_file(config_path))
		def get(key, default="", section="PrimeNet"):
			return config.get(section, key, fallback=default)
		engines = [name for name in ENGINES if config.getboolean("PrimeNet", name, fallback=False)]
		if len(engines) > 1:
			raise WorkspaceError("Configuration selects multiple computation programs.")
		engine = engines[0] if engines else None
		count = config.getint("PrimeNet", "NumWorkers", fallback=1)
		if not 1 <= count <= 128:
			raise WorkspaceError("Preview supports 1–128 workers.")
		work_name = get("work_file", "worktodo.txt")
		if not work_name or Path(work_name).name != work_name:
			raise WorkspaceError("Configured work file must be a filename, without a directory.")
		workers = []
		seen = set()
		for index in range(count):
			section = "Worker #{}".format(index + 1) if count > 1 else "PrimeNet"
			relative = get("directory", section=section)
			if engine == "prpll" and relative:
				raise WorkspaceError("PRPLL does not support configured worker directories.")
			if count > 1 and engine != "prpll" and not relative:
				raise WorkspaceError("Every worker needs a configured directory.")
			folder = (base / relative).resolve() if relative else base
			if not folder.is_dir():
				raise WorkspaceError("A configured worker directory does not exist.")
			if engine != "prpll" and folder in seen:
				raise WorkspaceError("Worker directories resolve to the same location.")
			seen.add(folder)
			work = folder / ("worktodo-{}.txt".format(index) if engine == "prpll" else work_name)
			workers.append({
				"number": index + 1, "directory": str(folder), "work_file": str(work),
				"preference": get("WorkPreference", section=section) or "Not configured",
				"work_present": work.is_file(),
			})
		identity = {"username": get("username") or "Not configured", "computer": get("ComputerID") or "Not configured"}
		request_state = config.getboolean("PrimeNet", "QuitGIMPS", fallback=False)
	except (ConfigError, ValueError, UnicodeError) as error:
		raise WorkspaceError("Configuration is malformed or contains invalid values.") from error
	usage = shutil.disk_usage(base)
	return {
		"directory": str(base), "config_present": config_path.is_file(), "config_name": config_name,
		"identity": identity, "engine": engine or "Not configured", "workers": workers,
		"new_work_disabled": request_state, "free_bytes": usage.free,
	}


def inspect_workspace(directory, config_name="prime.ini"):
	snapshot = workspace_snapshot(directory, config_name)
	all_lines = []
	worker_numbers = []
	for worker in snapshot["workers"]:
		path = Path(worker["work_file"])
		lines = read_small_file(path).splitlines() if worker["work_present"] else []
		# Ignore blank/comment lines for display; no file content is rewritten.
		lines = [line for line in lines if line.strip() and not line.lstrip().startswith(("#", ";"))]
		all_lines.extend(lines)
		worker_numbers.extend([worker["number"]] * len(lines))
		if len(all_lines) > 1000:
			raise WorkspaceError("Preview supports at most 1000 work lines across all workers.")
	parsed = backend_request("parse_work", lines=all_lines)["assignments"] if all_lines else []
	snapshot["assignments"] = [{"worker": number, **item} for number, item in zip(worker_numbers, parsed)]
	return snapshot


@contextmanager
def instance_lease(directory, filename="~lock"):
	"""Use the same byte/flock lock as the CLI, without truncating its file."""
	if filename not in {"~lock", "~gui-monitor.lock"}:
		raise ValueError("Unsupported instance lock name")
	path = Path(directory) / filename
	if path.is_symlink():
		raise WorkspaceError("Refusing a symbolic-link instance lock.")
	try:
		descriptor = os.open(path, os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0), 0o600)
		stream = os.fdopen(descriptor, "r+b")
	except OSError as error:
			raise WorkspaceError("Cannot open the AutoPrimeNet instance lock for this workspace.") from error
	try:
		try:
			if os.name == "nt":
				import msvcrt
				msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
			else:
				import fcntl
				fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
		except OSError as error:
			raise WorkspaceError("AutoPrimeNet or its scheduled runner is running, or its instance lock cannot be acquired. Stop it before changing the workspace.") from error
		yield
	finally:
		# Closing releases the OS lock. Never unlink the shared lock inode.
		stream.close()


def _file_version(path):
	if path.is_symlink():
		raise WorkspaceError("Configuration saving does not follow symbolic links.")
	try:
		before = path.stat()
	except FileNotFoundError:
		return None, b""
	if not stat.S_ISREG(before.st_mode):
		raise WorkspaceError("Configuration must be a regular file.")
	with path.open("rb") as stream:
		data = stream.read(MAX_FILE_BYTES + 1)
	if len(data) > MAX_FILE_BYTES:
		raise WorkspaceError("Configuration exceeds the 2 MiB size limit.")
	after = path.stat()
	identity = lambda value: (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns)
	if identity(before) != identity(after):
		raise WorkspaceError("Configuration changed while loading. Reload before editing.")
	return (*identity(after), hashlib.sha256(data).hexdigest()), data


def patch_ini(text, edits):
	"""Patch explicit single-line keys; preserve unrelated bytes and comments."""
	newline = "\r\n" if "\r\n" in text else "\n"
	lines = text.splitlines(keepends=True)
	sections = {}
	current = None
	positions = {}
	active = None
	active_indent = -1
	multiline = set()
	for index, line in enumerate(lines):
		if not line.strip() or line.lstrip().startswith(("#", ";")):
			continue
		indent = len(line.expandtabs()) - len(line.expandtabs().lstrip())
		if active is not None and indent > active_indent:
			multiline.add(active)
			continue
		header = re.match(r"^\s*\[([^]]+)\]", line)
		if header:
			if current is not None:
				sections[current] = (sections[current][0], index)
			current = header.group(1)
			sections[current] = (index, len(lines))
			active = None
			active_indent = -1
			continue
		if current is None or line.lstrip().startswith(("#", ";")):
			continue
		option = re.match(r"^(\s*)([^:=]+?)(\s*[:=]\s*)(.*?)(\r?\n)?$", line)
		if option:
			active = (current, option.group(2).strip())
			active_indent = indent
			positions[active] = (index, option)
	replace = {}
	insert = {}
	new_sections = {}
	for (section, key), value in edits.items():
		if value is not None and any(char in value for char in "\r\n\x00"):
			raise WorkspaceError("Configuration values must be single-line text.")
		if (section, key) in positions:
			index, match = positions[section, key]
			if (section, key) in multiline:
				raise WorkspaceError("A setting being edited has a multiline value; adjust it outside the GUI first.")
			replace[index] = "" if value is None else match.group(1) + match.group(2) + match.group(3) + value + (match.group(5) or "")
		elif value is not None:
			line = key + "=" + value + newline
			if section in sections:
				insert.setdefault(sections[section][1], []).append(line)
			else:
				new_sections.setdefault(section, []).append(line)
	result = []
	for index in range(len(lines) + 1):
		if index in insert:
			if result and not result[-1].endswith(("\n", "\r")):
				result.append(newline)
			result.extend(insert[index])
		if index < len(lines):
			result.append(replace.get(index, lines[index]))
	for section, additions in new_sections.items():
		if result and not result[-1].endswith(("\n", "\r")):
			result.append(newline)
		result.append("[" + section + "]" + newline)
		result.extend(additions)
	return "".join(result)


class ConfigDocument:
	"""An immutable loaded version plus typed, non-secret form values."""

	def __init__(self, directory, config_name="prime.ini"):
		self.directory = Path(directory).expanduser().resolve()
		if not self.directory.is_dir() or not config_name or Path(config_name).name != config_name or config_name in {".", "..", "~lock", "~gui-monitor.lock"}:
			raise WorkspaceError("Select an existing working directory and valid configuration filename.")
		if config_name.lower().endswith((".lck", ".proof", ".proof.tmp", ".add")):
			raise WorkspaceError("Configuration filename must not be a lock, proof or work-import file.")
		self.path = self.directory / config_name
		self.version, self.data = _file_version(self.path)
		self.bom = self.data.startswith(b"\xef\xbb\xbf")
		self.text = self.data.decode("utf-8-sig")
		self.config = ConfigParser()
		self.config.optionxform = str
		try:
			self.config.read_string(self.text)
		except ConfigError as error:
			raise WorkspaceError("Configuration is malformed; it was not opened for editing.") from error

	def values(self):
		return {field.key: self.config.get(field.section, field.ini_key, fallback=field.default) for field in FIELDS}

	def render(self, values, engine, workers):
		if engine not in ENGINES:
			raise WorkspaceError("Select one computation program.")
		if not 1 <= len(workers) <= 128:
			raise WorkspaceError("Configure 1–128 workers.")
		try:
			fields = validate_fields(values)
		except ValueError as error:
			raise WorkspaceError(str(error)) from error
		original = self.values()
		# Untouched fields keep their original spelling, interpolation and implicit
		# defaults. Saving one setting must not materialize every form default.
		edits = {}
		for field in FIELDS:
			before = original[field.key].strip() or None
			if field.kind == "boolean" and before is not None:
				before = str(self.config.getboolean(field.section, field.ini_key))
			if field.kind == "recipients" and before:
				before = ",".join(address.strip() for address in before.split(","))
			if fields[field.key] != before:
				edits[field.section, field.ini_key] = fields[field.key]
		for program in ENGINES:
			if program != engine:
				edits["PrimeNet", program] = None
			elif not self.config.getboolean("PrimeNet", program, fallback=False):
				edits["PrimeNet", program] = "True"
		if len(workers) != self.config.getint("PrimeNet", "NumWorkers", fallback=1):
			edits["PrimeNet", "NumWorkers"] = str(len(workers))
		for index, worker in enumerate(workers, 1):
			section = "Worker #{}".format(index) if len(workers) > 1 else "PrimeNet"
			directory = str(worker.get("directory", "")).strip()
			preference = str(worker.get("preference", "")).strip()
			if engine == "prpll" and directory:
				raise WorkspaceError("Clear worker directories when selecting PRPLL; it uses the working directory.")
			if any(char in directory for char in "\n\r\x00"):
				raise WorkspaceError("Worker directories must be single-line paths.")
			if preference:
				try:
					int(preference)
				except ValueError as error:
					raise WorkspaceError("Work preferences must be numeric codes or blank for the program default.") from error
			for key, value in (("directory", directory), ("WorkPreference", preference)):
				if value != self.config.get(section, key, fallback="").strip():
					edits[section, key] = value or None
		old_engines = [program for program in ENGINES if self.config.getboolean("PrimeNet", program, fallback=False)]
		if old_engines != [engine] or fields["CPUHours"] != self.config.get("PrimeNet", "CPUHours", fallback="24"):
			edits["Internals", "RollingAverage"] = "1000"
		if old_engines != [engine]:
			for section in ["Internals", *[name for name in self.config.sections() if re.fullmatch(r"Worker #\d+", name)]]:
				for key in ("msec_per_iter", "exponent"):
					edits[section, key] = None
		# Form entries are literal text. ConfigParser uses percent interpolation;
		# escape new literals while retaining untouched existing expressions.
		candidate = patch_ini(self.text, {key: value.replace("%", "%%") if value is not None else None for key, value in edits.items()})
		# Never let a chosen configuration path overwrite a known live data file.
		for index, worker in enumerate(workers):
			folder = (self.directory / worker.get("directory", "").strip()).resolve()
			names = [fields["work_file"] or "worktodo.txt", fields["results_file"] or ("results.json.txt" if engine in {"mfaktc", "mfakto", "primepath"} else "results.txt"), "certwork.txt", "results_sent.txt"]
			names += ["{}-{}.txt".format(stem, index) for stem in ("worktodo", "results", "certwork", "results_sent")]
			if self.path in [(folder / name).resolve() for name in names]:
				raise WorkspaceError("Configuration filename conflicts with a work, results or certification file.")
		if self.path == (self.directory / (fields["logfile"] or "autoprimenet.log")).resolve():
			raise WorkspaceError("Configuration filename conflicts with the activity log.")
		return candidate


def load_editor_workspace(directory, config_name="prime.ini"):
	document = ConfigDocument(directory, config_name)
	snapshot = inspect_workspace(directory, config_name)
	# Resolve every form value in the worker thread. A bad interpolation or bool
	# must be reported as a job failure, never break Tk's polling callback.
	try:
		values = document.values()
		for field in FIELDS:
			if field.kind == "boolean" and values[field.key]:
				document.config.getboolean(field.section, field.ini_key)
	except (ConfigError, ValueError) as error:
		raise WorkspaceError("Configuration contains an invalid form value or interpolation.") from error
	if _file_version(document.path)[0] != document.version:
		raise WorkspaceError("Configuration changed while loading. Reload before editing.")
	return {"document": document, "snapshot": snapshot}


def save_configuration(document, values, engine, workers):
	with instance_lease(document.directory, "~gui-monitor.lock"), instance_lease(document.directory):
		if _file_version(document.path)[0] != document.version:
			raise WorkspaceError("Configuration changed outside the GUI. Reload before saving.")
		if document.version is not None and (not document.path.stat().st_mode & 0o222 or not os.access(document.path, os.W_OK)):
			raise WorkspaceError("Configuration is read-only; no changes were saved.")
		text = document.render(values, engine, workers)
		backend_request("validate_config", text=text, directory=str(document.directory), config_name=document.path.name)
		data = (b"\xef\xbb\xbf" if document.bom else b"") + text.encode("utf-8")
		backup = None
		if data != document.data:
			if document.version is not None:
				with tempfile.NamedTemporaryFile(prefix=document.path.name + ".gui-backup-", suffix=".bak", dir=document.directory, delete=False) as stream:
					backup = stream.name
					stream.write(document.data)
					stream.flush()
					os.fsync(stream.fileno())
			temporary = None
			try:
				with tempfile.NamedTemporaryFile(prefix=".gui-config-", dir=document.directory, delete=False) as stream:
					temporary = stream.name
					stream.write(data)
					stream.flush()
					os.fsync(stream.fileno())
				mode = stat.S_IMODE(document.path.stat().st_mode) if document.version is not None else 0o600
				os.chmod(temporary, mode)
				if _file_version(document.path)[0] != document.version:
					raise WorkspaceError("Configuration changed during saving. Reload before retrying.")
				os.replace(temporary, document.path)
			finally:
				if temporary and Path(temporary).exists():
					Path(temporary).unlink()
		return {"document": ConfigDocument(str(document.directory), document.path.name), "backup": backup}
