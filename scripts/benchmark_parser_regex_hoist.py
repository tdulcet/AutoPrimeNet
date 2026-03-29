#!/usr/bin/env python3
"""Measure regex compile cost removed by hoisting parser patterns in autoprimenet.

autoprimenet.py is a script: importing it runs the full application (argparse, lock,
main loop). This script does not import autoprimenet. It uses the same pattern
strings as MLUCAS_STAT_* and GPUOWL_LOG_* — keep them in sync when patterns change.

Integration timing (parse_stat_file / parse_gpuowl_log_file end-to-end): use cProfile
on a real run, or compare two git revisions manually.

Run: python scripts/benchmark_parser_regex_hoist.py

Writes scripts/benchmark_parser_regex_hoist.txt on success (override with --output).
"""

from __future__ import annotations

import argparse
import re
import statistics
import sys
import time
from pathlib import Path
from typing import Tuple

_REPO = Path(__file__).resolve().parent.parent
_DEFAULT_RESULT_PATH = _REPO / "scripts" / "benchmark_parser_regex_hoist.txt"

# --- SYNC: autoprimenet.MLUCAS_STAT_* (3 patterns) ---
MLUCAS_STAT_PATTERNS = (
	r"(Iter#|S1|S2)(?: bit| at q)? = ([0-9]+) \[ ?([0-9]+\.[0-9]+)% complete\] .*\[ *([0-9]+\.[0-9]+) (m?sec)/iter\]",
	r"FFT length [0-9]{3,}K = ([0-9]{6,})",
	r"Stage 2 q0 = ([0-9]+)",
)

# --- SYNC: autoprimenet.GPUOWL_LOG_* (9 patterns) ---
GPUOWL_LOG_PATTERNS = (
	r"([0-9]{6,}) (LL|P1|OK|EE)? +([0-9]{4,})",
	r"([0-9]{6,})P1 +([0-9]+\.[0-9]+)% ([KE])? +[0-9a-f]{16} +([0-9]+)",
	r"\b([0-9]+) us/it;?",
	r"\b([0-9]{6,}) FFT: ([0-9]+(?:\.[0-9]+)?[KM])\b",
	r"\b[0-9]{6,} P1(?: B1=[0-9]+, B2=[0-9]+;|\([0-9]+(?:\.[0-9])?M?\)) ([0-9]+) bits;?\b",
	r"\b[0-9]{6,}P1 +[0-9]+\.[0-9]+% @([0-9]+)/([0-9]+) B1\([0-9]+\)",
	r"[0-9]{6,} P2\([0-9]+(?:\.[0-9])?M?,[0-9]+(?:\.[0-9])?M?\) ([0-9]+) blocks: ([0-9]+) - ([0-9]+);",
	r"\| P1\([0-9]+(?:\.[0-9])?M?\)",
	r"[0-9]{6,} P2(?: ([0-9]+)/([0-9]+)|\([0-9]+(?:\.[0-9])?M?,[0-9]+(?:\.[0-9])?M?\) OK @([0-9]+)):",
)


def _compile_all(patterns: Tuple[str, ...]) -> None:
	for p in patterns:
		re.compile(p)


def _bench_compile(patterns: Tuple[str, ...], repeat: int, number: int, warmup: int) -> Tuple[float, float]:
	for _ in range(warmup):
		_compile_all(patterns)
	times = []
	for _ in range(repeat):
		t0 = time.perf_counter()
		for _ in range(number):
			_compile_all(patterns)
		t1 = time.perf_counter()
		times.append((t1 - t0) / number)
	return min(times), statistics.mean(times)


def main() -> int:
	ap = argparse.ArgumentParser(description=__doc__)
	ap.add_argument("--iterations", type=int, default=20_000, help="outer loops per repeat (default 20000)")
	ap.add_argument("--repeat", type=int, default=7, help="timing repeats (default 7)")
	ap.add_argument("--warmup", type=int, default=2, help="warmup outer loops (default 2)")
	ap.add_argument("--gpuowl-only", action="store_true")
	ap.add_argument("--mlucas-only", action="store_true")
	ap.add_argument(
		"--output",
		"-o",
		type=Path,
		default=_DEFAULT_RESULT_PATH,
		help="write result summary to this file (default: scripts/benchmark_parser_regex_hoist.txt)",
	)
	args = ap.parse_args()

	n = args.iterations
	r = args.repeat
	w = args.warmup

	intro = (
		"Cost per simulated parse_* call = compiling all patterns for that parser "
		"(pre-hoist behavior). Post-hoist: 0 compiles; savings ~= these times.\n"
	)
	print(intro)

	mlucas_best_us = mlucas_mean_us = None
	gpuowl_best_us = gpuowl_mean_us = None

	if not args.gpuowl_only:
		best, mean = _bench_compile(MLUCAS_STAT_PATTERNS, r, n, w)
		mlucas_best_us, mlucas_mean_us = best * 1e6, mean * 1e6
		print("parse_stat_file pattern set (3 x re.compile per call, pre-hoist)")
		print("  best of {}: {:.3f} us/simulated-call  |  mean: {:.3f} us".format(r, mlucas_best_us, mlucas_mean_us))
		print()

	if not args.mlucas_only:
		best, mean = _bench_compile(GPUOWL_LOG_PATTERNS, r, n, w)
		gpuowl_best_us, gpuowl_mean_us = best * 1e6, mean * 1e6
		print("parse_gpuowl_log_file pattern set (9 x re.compile per call, pre-hoist)")
		print("  best of {}: {:.3f} us/simulated-call  |  mean: {:.3f} us".format(r, gpuowl_best_us, gpuowl_mean_us))
		print()

	py_ver = sys.version.split()[0]
	print("Python {}".format(py_ver))
	note = (
		"Note: Log/stat .search() work dominates on large files; "
		"this isolates compile overhead only."
	)
	print(note)

	lines = [
		"mode=benchmark_parser_regex_hoist",
		"time_iso={}".format(time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime())),
		"python={}".format(py_ver),
		"iterations={}".format(n),
		"repeat={}".format(r),
		"warmup={}".format(w),
		"gpuowl_only={}".format(int(args.gpuowl_only)),
		"mlucas_only={}".format(int(args.mlucas_only)),
	]
	if mlucas_best_us is not None:
		lines.extend(
			[
				"parse_stat_patterns=3",
				"parse_stat_us_per_simulated_call_best={:.6f}".format(mlucas_best_us),
				"parse_stat_us_per_simulated_call_mean={:.6f}".format(mlucas_mean_us),
			]
		)
	if gpuowl_best_us is not None:
		lines.extend(
			[
				"parse_gpuowl_patterns=9",
				"parse_gpuowl_us_per_simulated_call_best={:.6f}".format(gpuowl_best_us),
				"parse_gpuowl_us_per_simulated_call_mean={:.6f}".format(gpuowl_mean_us),
			]
		)
	lines.extend(["", intro.rstrip("\n"), ""])
	if mlucas_best_us is not None:
		lines.extend(
			[
				"parse_stat_file pattern set (3 x re.compile per call, pre-hoist)",
				"  best of {}: {:.3f} us/simulated-call  |  mean: {:.3f} us".format(r, mlucas_best_us, mlucas_mean_us),
				"",
			]
		)
	if gpuowl_best_us is not None:
		lines.extend(
			[
				"parse_gpuowl_log_file pattern set (9 x re.compile per call, pre-hoist)",
				"  best of {}: {:.3f} us/simulated-call  |  mean: {:.3f} us".format(r, gpuowl_best_us, gpuowl_mean_us),
				"",
			]
		)
	lines.extend(["Python {}".format(py_ver), note])

	out_path = args.output.expanduser()
	out_path.parent.mkdir(parents=True, exist_ok=True)
	out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
	print("Wrote results to {!r}".format(str(out_path)))
	return 0


if __name__ == "__main__":
	sys.exit(main())
