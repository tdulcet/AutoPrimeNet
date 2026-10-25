"""Read-only workspace discovery for the GUI foundation.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from configparser import ConfigParser, Error as ConfigError
from pathlib import Path
import shutil

from gui_controller import backend_request


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
