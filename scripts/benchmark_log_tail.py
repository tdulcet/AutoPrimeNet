#!/usr/bin/env python3
"""Benchmark log tail and GpuOwl log scan: legacy (pre-change) vs autoprimenet --benchmark-log-io (post).

Pre-change baseline (full-file read + deque tail, full list + reversed parse scan):
  python scripts/benchmark_log_tail.py --legacy-only
  (writes scripts/benchmark_log_io_pre.txt by default; override with --out / -o)

Post-change (delegates to autoprimenet.py --benchmark-log-io):
  python scripts/benchmark_log_tail.py --subprocess
  (writes scripts/benchmark_log_io_post.txt by default)

Manual run (repeat must precede --benchmark-log-io because the latter uses nargs=*):
  python autoprimenet.py --benchmark-repeat 5 --benchmark-log-io C:\\path\\to\\logfiles

Default corpus: sibling of repo AutoPrimeNet -> ../logfiles (override with paths).
Paths, globs, tail line count, and output files: see CONFIG block near the top of this script.
"""

from __future__ import annotations

import argparse
import glob
import io
import os
import subprocess
import sys
import tempfile
import time
from collections import deque
from pathlib import Path

_REPO = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Configuration — edit paths and defaults here (CLI flags override where noted).
# ---------------------------------------------------------------------------
# When no paths are given on the command line, this directory is scanned.
DEFAULT_LOGFILES_DIR: Path = _REPO.parent / "logfiles"
# Globs appended when a directory is passed or used as default:
GLOB_GPUOWL_LOG = "gpuowl*.log"
GLOB_STAT = "p*.stat"
# autoprimenet subprocess benchmark:
AUTOPRIMENET_SCRIPT = _REPO / "autoprimenet.py"
# Legacy tail / deque uses this many lines:
TAIL_LINE_COUNT = 100
TEXT_ENCODING = "utf-8"
TEXT_ERRORS = "replace"
# Default output files (override with --out / -o):
DEFAULT_RESULT_LEGACY = _REPO / "scripts" / "benchmark_log_io_pre.txt"
DEFAULT_RESULT_SUBPROCESS = _REPO / "scripts" / "benchmark_log_io_post.txt"
DEFAULT_BENCHMARK_REPEAT = 5
DEFAULT_LEGACY_WARMUP = 1
# ---------------------------------------------------------------------------


def _default_logfiles_dir() -> str:
	return str(DEFAULT_LOGFILES_DIR)


def _expand_paths(paths: list[str]) -> list[str]:
	out: list[str] = []
	for p in paths:
		p = os.path.normpath(p)
		if os.path.isdir(p):
			out.extend(glob.glob(os.path.join(p, GLOB_GPUOWL_LOG)))
			out.extend(glob.glob(os.path.join(p, GLOB_STAT)))
		elif os.path.isfile(p):
			out.append(p)
	return sorted(set(out))


def _readonly_lines(filename: str, errors: str | None = None):
	if errors is None:
		errors = TEXT_ERRORS
	try:
		with io.open(filename, "r", encoding=TEXT_ENCODING, errors=errors) as f:
			for line in f:
				yield line.rstrip("\n")
	except OSError:
		return


def _legacy_tail(filename: str, n: int) -> str:
	if not os.path.isfile(filename):
		return "> (File not found)"
	w = deque(_readonly_lines(filename), n)
	if not w:
		return "> (File is empty)"
	return "\n".join("> " + line for line in w)


def _legacy_full_lines(filename: str) -> list[str]:
	return list(_readonly_lines(filename))


def _time_repeat(fn, repeat: int, warmup: int) -> tuple[float, object]:
	for _ in range(warmup):
		fn()
	t0 = time.perf_counter()
	last = None
	for _ in range(repeat):
		last = fn()
	return time.perf_counter() - t0, last


def _run_legacy(paths: list[str], repeat: int, warmup: int) -> str:
	lines_out: list[str] = []
	lines_out.append("mode=legacy_full_file_read")
	lines_out.append("repeat={} warmup={}".format(repeat, warmup))
	for path in paths:
		if not os.path.isfile(path):
			continue
		size = os.path.getsize(path)
		base = os.path.basename(path)
		t_tail, _ = _time_repeat(lambda: _legacy_tail(path, TAIL_LINE_COUNT), repeat, warmup)
		lines_out.append(
			"file={!r} bytes={} tail{}_total_sec={:.6f} tail{}_mean_sec={:.6f}".format(
				base, size, TAIL_LINE_COUNT, t_tail, TAIL_LINE_COUNT, t_tail / repeat
			)
		)
		if base.endswith(".log") and "gpuowl" in base.lower():
			t_full, lines = _time_repeat(lambda: _legacy_full_lines(path), repeat, warmup)
			lines_out.append(
				"  full_read_lines_total_sec={:.6f} full_read_mean_sec={:.6f} n_lines={}".format(t_full, t_full / repeat, len(lines))
			)
			t_rev, _ = _time_repeat(lambda: list(reversed(lines)), repeat, warmup)
			lines_out.append("  reversed_list_total_sec={:.6f} reversed_list_mean_sec={:.6f}".format(t_rev, t_rev / repeat))
	return "\n".join(lines_out) + "\n"


def _run_subprocess(paths: list[str], repeat: int) -> str:
	ap = str(AUTOPRIMENET_SCRIPT)
	# --benchmark-repeat must come before --benchmark-log-io (nargs=* would swallow it).
	cmd = [sys.executable, ap, "--benchmark-repeat", str(repeat), "--benchmark-log-io"]
	cmd.extend(paths)
	r = subprocess.run(cmd, cwd=str(_REPO), capture_output=True, text=True)
	out = (r.stdout or "") + (r.stderr or "")
	if r.returncode != 0:
		out += "\nEXIT_CODE={}\n".format(r.returncode)
	return out


def main() -> int:
	ap = argparse.ArgumentParser(description=__doc__)
	ap.add_argument("paths", nargs="*", help="Log/stat files or directories (default: ../logfiles)")
	ap.add_argument("--legacy-only", action="store_true", help="Time legacy full-file tail/read (pre-change baseline)")
	ap.add_argument("--subprocess", action="store_true", help="Run autoprimenet.py --benchmark-log-io (post-change)")
	ap.add_argument("--repeat", type=int, default=DEFAULT_BENCHMARK_REPEAT)
	ap.add_argument("--warmup", type=int, default=DEFAULT_LEGACY_WARMUP)
	ap.add_argument(
		"--out",
		"--output",
		"-o",
		type=Path,
		default=None,
		help=(
			"write benchmark output to this file (default: scripts/benchmark_log_io_pre.txt "
			"for legacy, scripts/benchmark_log_io_post.txt for --subprocess)"
		),
	)
	args = ap.parse_args()
	if args.out is None:
		args.out = DEFAULT_RESULT_SUBPROCESS if args.subprocess else DEFAULT_RESULT_LEGACY

	paths = _expand_paths(args.paths if args.paths else [_default_logfiles_dir()])
	if not paths:
		print("No log/stat files found.", file=sys.stderr)
		return 1

	if args.legacy_only and args.subprocess:
		print("Use only one of --legacy-only or --subprocess", file=sys.stderr)
		return 1

	if args.subprocess:
		text = _run_subprocess(paths, args.repeat)
	else:
		text = _run_legacy(paths, args.repeat, args.warmup)

	print(text, end="")
	out_path = args.out.expanduser()
	out_path.parent.mkdir(parents=True, exist_ok=True)
	py_ver = sys.version.split()[0]
	header = "time_iso={}\npython={}\n".format(
		time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime()),
		py_ver,
	)
	body = text if text.endswith("\n") else text + "\n"
	out_path.write_text(header + body, encoding="utf-8")
	print("Wrote results to {!r}".format(str(out_path)))
	return 0


if __name__ == "__main__":
	sys.exit(main())
