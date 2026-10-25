"""Private point-in-time work snapshots before recovery or unreservation.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import tempfile
import time

from gui_config import WorkspaceError, workspace_snapshot


MAX_SNAPSHOT_FILE = 2 * 1024 * 1024
MAX_SNAPSHOT_TOTAL = 16 * 1024 * 1024


def _version(info):
	return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def _read(path):
	try:
		before = path.lstat()
	except FileNotFoundError:
		return None, None
	if not stat.S_ISREG(before.st_mode):
		raise WorkspaceError("Assignment snapshots require regular, non-symlink work/certification files.")
	if before.st_size > MAX_SNAPSHOT_FILE:
		raise WorkspaceError("A work/certification file exceeds the 2 MiB assignment snapshot limit.")
	with os.fdopen(os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)), "rb") as stream:
		if _version(os.fstat(stream.fileno())) != _version(before):
			raise WorkspaceError("An assignment file changed during backup. Pause computation and retry.")
		data = stream.read(MAX_SNAPSHOT_FILE + 1)
		if len(data) > MAX_SNAPSHOT_FILE or _version(os.fstat(stream.fileno())) != _version(before):
			raise WorkspaceError("An assignment file changed during backup. Pause computation and retry.")
	return data, _version(before)


def snapshot_assignments(directory, config_name, operation, parameters=None):
	"""Fail closed on unsafe/changing inputs; never alter the original files."""
	snapshot = workspace_snapshot(directory, config_name)
	folder = Path(tempfile.mkdtemp(prefix=".gui-assignment-backup-", dir=directory))
	try:
		entries, versions = [], []
		total = 0
		for worker in snapshot["workers"]:
			work = Path(worker["work_file"])
			cert = work.parent / ("certwork-{}.txt".format(worker["number"] - 1) if snapshot["engine"] == "prpll" else "certwork.txt")
			for role, path in (("work", work), ("certification", cert)):
				data, version = _read(path)
				versions.append((path, version))
				entry = {"worker": worker["number"], "role": role, "original_path": str(path), "present": data is not None}
				if data is not None:
					total += len(data)
					if total > MAX_SNAPSHOT_TOTAL:
						raise WorkspaceError("Assignment snapshots exceed the 16 MiB total limit.")
					name = "worker-{}-{}.bin".format(worker["number"], role)
					with open(folder / name, "xb", opener=lambda path, flags: os.open(path, flags, 0o600)) as stream:
						stream.write(data)
						stream.flush()
						os.fsync(stream.fileno())
					entry.update(backup_file=name, size=len(data), sha256=hashlib.sha256(data).hexdigest())
				entries.append(entry)
		# Recheck every input after all reads, including files initially absent.
		for path, version in versions:
			try:
				current = _version(path.lstat())
			except FileNotFoundError:
				current = None
			if current != version:
				raise WorkspaceError("Assignment files changed during backup. Pause computation and retry.")
		manifest = {"format": 1, "operation": operation, "parameters": parameters or {}, "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "files": entries}
		with open(folder / "manifest.json", "x", encoding="utf-8", opener=lambda path, flags: os.open(path, flags, 0o600)) as stream:
			json.dump(manifest, stream, indent=2)
			stream.write("\n")
			stream.flush()
			os.fsync(stream.fileno())
		return str(folder)
	except BaseException:
		shutil.rmtree(folder)
		raise
