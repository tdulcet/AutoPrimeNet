"""Reject overlapping GUI-managed configuration and runtime file roles.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import os
from pathlib import Path
import stat
import sys
import unicodedata


def path_key(path):
	"""Account for the actual macOS volume's filename comparison policy."""
	value = os.path.normcase(str(path))
	if sys.platform == "darwin":
		parent = path.parent
		while not parent.exists() and parent != parent.parent:
			parent = parent.parent
		# Darwin's sys/unistd.h defines _PC_CASE_SENSITIVE as 11. Python's
		# pathconf_names does not expose this platform-specific constant.
		if os.pathconf(parent, 11) != 1:
			value = unicodedata.normalize("NFD", value).casefold()
	return value


def validate_paths(directory, config_name, args):
	"""Check effective upstream filenames, including indexed PRPLL workers."""
	base = Path(directory).resolve()
	folders = [(base / item).resolve() for item in args.dirs] if args.dirs else [base]
	paths = [("configuration", base / config_name)]
	paths.extend(("instance ownership", base / name) for name in ("~lock", "~gui-monitor.lock", ".gui-runner.guard"))
	if args.logfile:
		paths.append(("activity log", base / args.logfile))
		# The audited CLI uses RotatingFileHandler with five backups.
		paths.extend(("rotated activity log", base / (args.logfile + f".{index}")) for index in range(1, 6))
	for index in range(args.num_workers):
		folder = base if args.prpll else folders[index if len(folders) > 1 else 0]
		names = {
			"work": f"worktodo-{index}.txt" if args.prpll else args.work_file,
			"results": f"results-{index}.txt" if args.prpll else args.results_file,
			"certification": f"certwork-{index}.txt" if args.prpll else "certwork.txt",
			"sent-results history": f"results_sent-{index}.txt" if args.prpll else "results_sent.txt",
		}
		for role, name in names.items():
			path = folder / name
			paths.append((f"worker {index + 1} {role}", path))
			if role in {"work", "certification"}:
				add = path.with_suffix(".add")
				paths.append((f"worker {index + 1} {role} import", add))
				paths.append((f"worker {index + 1} {role} import lock", Path(str(add) + ".lck")))
			paths.append((f"worker {index + 1} {role} lock", Path(str(path) + ".lck")))
	if args.archive_dir:
		paths.append(("proof archive directory", base / args.archive_dir))
	seen_paths, seen_files = {}, {}
	for role, path in paths:
		resolved = path.resolve()
		key = path_key(resolved)
		other = seen_paths.get(key)
		try:
			info = resolved.stat()
		except FileNotFoundError:
			info = None
		if info is not None and not (stat.S_ISDIR(info.st_mode) if role == "proof archive directory" else stat.S_ISREG(info.st_mode)):
			raise ValueError(f"The {role} path must be a {'directory' if role == 'proof archive directory' else 'regular file'}.")
		if info is not None and info.st_ino:
			inode = (info.st_dev, info.st_ino)
			other = other or seen_files.get(inode)
			seen_files[inode] = role
		if other:
			raise ValueError(f"File paths conflict: {other} and {role}. Choose separate paths before saving or starting AutoPrimeNet.")
		seen_paths[key] = role
