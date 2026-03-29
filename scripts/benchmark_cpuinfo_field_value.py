#!/usr/bin/env python3
"""Micro-benchmark: /proc/cpuinfo value parsing (see autoprimenet._cpuinfo_field_value).

Compares:
  - Original: re.sub(r"^.*: *", "", line.rstrip(), count=1)
  - Strict equivalent: cpuinfo_field_value (string scan)
  - Not equivalent shortcuts (documented in autoprimenet): split + lstrip(" ") / strip()
    Those one-liners only work when ":" is present; batch B uses only such lines.

Writes scripts/benchmark_cpuinfo_field_value.txt on success (override with --output).
"""

from __future__ import annotations

import argparse
import re
import statistics
import sys
import time
from pathlib import Path

_REPO = Path(__file__).resolve().parent.parent
_DEFAULT_RESULT_PATH = _REPO / "scripts" / "benchmark_cpuinfo_field_value.txt"

PATTERN = r"^.*: *"


def re_sub_original(line: str) -> str:
	return re.sub(PATTERN, "", line.rstrip(), count=1)


def cpuinfo_field_value(line: str) -> str:
	# Same algorithm as autoprimenet._cpuinfo_field_value
	s = line.rstrip()
	colon = s.find(":")
	if colon < 0:
		return s
	i = colon + 1
	n = len(s)
	while i < n and s[i] == " ":
		i += 1
	return s[i:]


def shortcut_split_lstrip(line: str) -> str:
	"""Not strictly equivalent: raises if no ':'; lstrip(\" \") != regex `` *`` after ':'; etc."""
	s = line.rstrip()
	return s.split(":", 1)[1].lstrip(" ")


def shortcut_split_strip(line: str) -> str:
	"""Not strictly equivalent: same as lstrip variant plus full Unicode strip on value edges."""
	s = line.rstrip()
	return s.split(":", 1)[1].strip()


SAMPLES = [
	"model name\t: Intel(R) Core(TM) i7-9700K CPU @ 3.60GHz\n",
	"cpu MHz\t\t: 3600.000\n",
	"model name        : AMD Ryzen 9 5950X 16-Core Processor\n",
	"cpu MHz         : 2200.000\n",
	"bogus line without delimiter\n",
	"key:  \tvalue with tab after spaces\n",
]

# One-liners that use split(":", 1)[1] cannot handle lines with no colon.
SAMPLES_WITH_COLON = [s for s in SAMPLES if ":" in s.rstrip()]


def bench(fn, lines: list[str], repeat: int = 7, number: int = 50_000) -> tuple[float, float]:
	"""Return (best_sec_per_loop, mean_sec_per_loop) for timeit-style inner loop."""
	times = []
	for _ in range(repeat):
		t0 = time.perf_counter()
		for _ in range(number):
			for line in lines:
				fn(line)
		t1 = time.perf_counter()
		times.append((t1 - t0) / number)
	return min(times), statistics.mean(times)


def main() -> int:
	ap = argparse.ArgumentParser(description=__doc__)
	ap.add_argument(
		"--output",
		"-o",
		type=Path,
		default=_DEFAULT_RESULT_PATH,
		help="write result summary to this file (default: scripts/benchmark_cpuinfo_field_value.txt)",
	)
	args = ap.parse_args()

	for line in SAMPLES:
		a, b = re_sub_original(line), cpuinfo_field_value(line)
		assert a == b, (repr(line), a, b)

	n = 50_000
	r = 7
	parses_all = len(SAMPLES)
	parses_colon = len(SAMPLES_WITH_COLON)

	print("=== Batch A: all sample lines (strict must match re.sub) ===")
	print(f"Lines per batch: {parses_all}; outer iterations: {n}; repeats: {r}")
	print()

	regex_b, regex_m = bench(re_sub_original, SAMPLES, repeat=r, number=n)
	str_b, str_m = bench(cpuinfo_field_value, SAMPLES, repeat=r, number=n)
	speedup_a = regex_b / str_b

	print("re.sub(r'^.*: *', '', line.rstrip(), count=1)  [original]")
	print(f"  best: {regex_b*1e6:.3f} us/batch  |  {parses_all / regex_b / 1e6:.2f} M parses/s")
	print(f"  mean: {regex_m*1e6:.3f} us/batch")
	print()
	print("cpuinfo_field_value (strict equivalent)")
	print(f"  best: {str_b*1e6:.3f} us/batch  |  {parses_all / str_b / 1e6:.2f} M parses/s")
	print(f"  mean: {str_m*1e6:.3f} us/batch")
	print()
	print(f"Speedup vs original (best): {speedup_a:.2f}x")
	print()

	print("=== Batch B: only lines containing ':' (shortcuts are defined) ===")
	print(
		f"Lines per batch: {parses_colon} (excludes no-colon lines that would raise on split()[1]); "
		f"outer iterations: {n}; repeats: {r}"
	)
	print("NOTE: shortcut outputs may differ from re.sub on some lines; this is timing only.")
	print()

	r2_b, r2_m = bench(re_sub_original, SAMPLES_WITH_COLON, repeat=r, number=n)
	s2_b, s2_m = bench(cpuinfo_field_value, SAMPLES_WITH_COLON, repeat=r, number=n)
	ls_b, ls_m = bench(shortcut_split_lstrip, SAMPLES_WITH_COLON, repeat=r, number=n)
	st_b, st_m = bench(shortcut_split_strip, SAMPLES_WITH_COLON, repeat=r, number=n)
	sp_strict = r2_b / s2_b
	sp_lstrip = r2_b / ls_b
	sp_strip = r2_b / st_b

	def row(label: str, best: float, mean: float) -> None:
		print(f"{label}")
		print(f"  best: {best*1e6:.3f} us/batch  |  {parses_colon / best / 1e6:.2f} M parses/s")
		print(f"  mean: {mean*1e6:.3f} us/batch")

	row("re.sub  [original]", r2_b, r2_m)
	print()
	row("cpuinfo_field_value  [strict]", s2_b, s2_m)
	print()
	row('line.rstrip().split(":", 1)[1].lstrip(" ")  [shortcut]', ls_b, ls_m)
	print()
	row('line.rstrip().split(":", 1)[1].strip()  [shortcut]', st_b, st_m)
	print()
	print("Speedup vs original re.sub (best, batch B):")
	print(f"  strict string:     {sp_strict:.2f}x")
	print(f"  split + lstrip:    {sp_lstrip:.2f}x")
	print(f"  split + strip:     {sp_strip:.2f}x")

	py_ver = sys.version.split()[0]
	lines = [
		"mode=benchmark_cpuinfo_field_value",
		"time_iso={}".format(time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime())),
		"python={}".format(py_ver),
		"batch_a_lines={}".format(parses_all),
		"batch_b_lines={}".format(parses_colon),
		"outer_iterations={}".format(n),
		"repeat={}".format(r),
		"batch_a_regex_us_best={:.6f}".format(regex_b * 1e6),
		"batch_a_regex_us_mean={:.6f}".format(regex_m * 1e6),
		"batch_a_strict_us_best={:.6f}".format(str_b * 1e6),
		"batch_a_strict_us_mean={:.6f}".format(str_m * 1e6),
		"batch_a_speedup_regex_over_strict={:.6f}".format(speedup_a),
		"batch_b_regex_us_best={:.6f}".format(r2_b * 1e6),
		"batch_b_regex_us_mean={:.6f}".format(r2_m * 1e6),
		"batch_b_strict_us_best={:.6f}".format(s2_b * 1e6),
		"batch_b_strict_us_mean={:.6f}".format(s2_m * 1e6),
		"batch_b_lstrip_us_best={:.6f}".format(ls_b * 1e6),
		"batch_b_lstrip_us_mean={:.6f}".format(ls_m * 1e6),
		"batch_b_strip_us_best={:.6f}".format(st_b * 1e6),
		"batch_b_strip_us_mean={:.6f}".format(st_m * 1e6),
		"batch_b_speedup_regex_over_strict={:.6f}".format(sp_strict),
		"batch_b_speedup_regex_over_lstrip={:.6f}".format(sp_lstrip),
		"batch_b_speedup_regex_over_strip={:.6f}".format(sp_strip),
		"",
		"=== Batch A: all sample lines (strict must match re.sub) ===",
		f"Lines per batch: {parses_all}; outer iterations: {n}; repeats: {r}",
		"",
		"re.sub(r'^.*: *', '', line.rstrip(), count=1)  [original]",
		f"  best: {regex_b*1e6:.3f} us/batch  |  {parses_all / regex_b / 1e6:.2f} M parses/s",
		f"  mean: {regex_m*1e6:.3f} us/batch",
		"",
		"cpuinfo_field_value (strict equivalent)",
		f"  best: {str_b*1e6:.3f} us/batch  |  {parses_all / str_b / 1e6:.2f} M parses/s",
		f"  mean: {str_m*1e6:.3f} us/batch",
		"",
		f"Speedup vs original (best): {speedup_a:.2f}x",
		"",
		"=== Batch B: only lines containing ':' (shortcuts are defined) ===",
		f"Lines per batch: {parses_colon} (excludes no-colon lines that would raise on split()[1]); "
		f"outer iterations: {n}; repeats: {r}",
		"NOTE: shortcut outputs may differ from re.sub on some lines; this is timing only.",
		"",
		"re.sub  [original]",
		f"  best: {r2_b*1e6:.3f} us/batch  |  {parses_colon / r2_b / 1e6:.2f} M parses/s",
		f"  mean: {r2_m*1e6:.3f} us/batch",
		"",
		"cpuinfo_field_value  [strict]",
		f"  best: {s2_b*1e6:.3f} us/batch  |  {parses_colon / s2_b / 1e6:.2f} M parses/s",
		f"  mean: {s2_m*1e6:.3f} us/batch",
		"",
		'line.rstrip().split(":", 1)[1].lstrip(" ")  [shortcut]',
		f"  best: {ls_b*1e6:.3f} us/batch  |  {parses_colon / ls_b / 1e6:.2f} M parses/s",
		f"  mean: {ls_m*1e6:.3f} us/batch",
		"",
		'line.rstrip().split(":", 1)[1].strip()  [shortcut]',
		f"  best: {st_b*1e6:.3f} us/batch  |  {parses_colon / st_b / 1e6:.2f} M parses/s",
		f"  mean: {st_m*1e6:.3f} us/batch",
		"",
		"Speedup vs original re.sub (best, batch B):",
		f"  strict string:     {sp_strict:.2f}x",
		f"  split + lstrip:    {sp_lstrip:.2f}x",
		f"  split + strip:     {sp_strip:.2f}x",
		"",
		"Python {}".format(py_ver),
	]

	out_path = args.output.expanduser()
	out_path.parent.mkdir(parents=True, exist_ok=True)
	out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
	print()
	print("Wrote results to {!r}".format(str(out_path)))
	return 0


if __name__ == "__main__":
	sys.exit(main())
