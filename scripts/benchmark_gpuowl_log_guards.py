#!/usr/bin/env python3
"""Benchmark GpuOwl log parsing: unconditional regex .search vs substring guards.

Mirrors the control flow of parse_gpuowl_log_file (autoprimenet.py log loop ~5949–6026): same
line order (reversed file), same branches, early break on wrong exponent, P1_PIPE only
inside the res+us_res branch. Does not run savefile / glob logic.

Per log file, exponent p is taken from the first MAIN or AP1 match scanning from the
end of the file (same context as a live assignment reading gpuowl.log).

Accuracy: compares parse result tuple guarded vs unguarded; runs validate_gpuowl_log_guards.py.

Run: python scripts/benchmark_gpuowl_log_guards.py

Writes scripts/benchmark_gpuowl_log_guards.txt on success (override with --output).
"""

from __future__ import annotations

import argparse
import re
import statistics
import subprocess
import sys
import time
from decimal import Decimal
from pathlib import Path
from statistics import median_low

_REPO = Path(__file__).resolve().parent.parent
_DEFAULT_RESULT_PATH = _REPO / "scripts" / "benchmark_gpuowl_log_guards.txt"

# --- SYNC: autoprimenet suffix_power + INPUT_UNIT_RE + input_unit(scale=False) ---
_SUFFIX_POWER = {"k": 1, "K": 1, "M": 2, "G": 3, "T": 4, "P": 5, "E": 6, "Z": 7, "Y": 8, "R": 9, "Q": 10}
_INPUT_UNIT_RE = re.compile(r"^([0-9]+(?:\.[0-9]+)?)(?:\s*([" + "".join(_SUFFIX_POWER) + r"])i?)?$")


def _input_unit(astr: str) -> int:
	scale_base = 1024
	m = _INPUT_UNIT_RE.match(astr)
	if not m:
		raise ValueError("Invalid number or suffix: {!r}".format(astr))
	number, unit = m.groups()
	if unit:
		return int(Decimal(number) * scale_base ** _SUFFIX_POWER[unit])
	return int(number)


# --- SYNC: autoprimenet _gpuowl_log_need_* ---
_MAIN_GUARD_RE = re.compile(r"\d{6,}.*\d{4,}")


def _need_main(line: str) -> bool:
	return _MAIN_GUARD_RE.search(line) is not None


def _need_ap1(line: str) -> bool:
	i = line.find("P1 ")
	if i < 1 or not line[i - 1].isdigit():
		return False
	j = i - 1
	while j >= 0 and line[j].isdigit():
		j -= 1
	return i - 1 - j >= 6


def _need_us(line: str) -> bool:
	return " us/it" in line


def _need_fft(line: str) -> bool:
	return " FFT:" in line


def _need_p1_bits(line: str) -> bool:
	return (" bits" in line or "bits;" in line) and (" P1" in line or "P1(" in line)


def _need_ap1_bits(line: str) -> bool:
	return "P1" in line and "%" in line and "B1(" in line


def _need_p2_blocks(line: str) -> bool:
	return "blocks:" in line and "P2(" in line


def _need_p2_ok(line: str) -> bool:
	return " P2(" in line or ("/" in line and " P2 " in line)


def _need_p1_pipe(line: str) -> bool:
	return "| P1(" in line


# --- SYNC: autoprimenet.GPUOWL_LOG_* ---
_RE_MAIN = re.compile(r"([0-9]{6,}) (LL|P1|OK|EE)? +([0-9]{4,})")
_RE_AP1 = re.compile(r"([0-9]{6,})P1 +([0-9]+\.[0-9]+)% ([KE])? +[0-9a-f]{16} +([0-9]+)")
_RE_US = re.compile(r"\b([0-9]+) us/it;?")
_RE_FFT = re.compile(r"\b([0-9]{6,}) FFT: ([0-9]+(?:\.[0-9]+)?[KM])\b")
_RE_P1_BITS = re.compile(
	r"\b[0-9]{6,} P1(?: B1=[0-9]+, B2=[0-9]+;|\([0-9]+(?:\.[0-9])?M?\)) ([0-9]+) bits;?\b"
)
_RE_AP1_BITS = re.compile(r"\b[0-9]{6,}P1 +[0-9]+\.[0-9]+% @([0-9]+)/([0-9]+) B1\([0-9]+\)")
_RE_P2_BLOCKS = re.compile(
	r"[0-9]{6,} P2\([0-9]+(?:\.[0-9])?M?,[0-9]+(?:\.[0-9])?M?\) ([0-9]+) blocks: ([0-9]+) - ([0-9]+);"
)
_RE_P1_PIPE = re.compile(r"\| P1\([0-9]+(?:\.[0-9])?M?\)")
_RE_P2_OK = re.compile(
	r"[0-9]{6,} P2(?: ([0-9]+)/([0-9]+)|\([0-9]+(?:\.[0-9])?M?,[0-9]+(?:\.[0-9])?M?\) OK @([0-9]+)):"
)


class _NoopAdapter:
	def debug(self, *args, **kwargs):
		pass


def _detect_p_from_log_end(lines: list[str]) -> int | None:
	for line in reversed(lines):
		r = _RE_MAIN.search(line)
		if r:
			return int(r.group(1))
		a = _RE_AP1.search(line)
		if a:
			return int(a.group(1))
	return None


def _parse_gpuowl_log_sim(lines: list[str], p: int, use_guards: bool) -> tuple:
	"""Return (result_tuple, n_regex_searches). Mirrors parse_gpuowl_log_file log loop."""
	adapter = _NoopAdapter()
	n_search = 0

	def log_search(pat, line, need):
		nonlocal n_search
		if use_guards and not need(line):
			return None
		n_search += 1
		return pat.search(line)

	iteration = 0
	iterations = stage = None
	fftlen = None
	found = 0
	list_usec_per_iter = []
	p1 = p2 = False
	buffs = bits = 0
	percent = 0.0

	for line in reversed(lines):
		res = log_search(_RE_MAIN, line, _need_main)
		ares = log_search(_RE_AP1, line, _need_ap1)
		us_res = log_search(_RE_US, line, _need_us)
		fft_res = log_search(_RE_FFT, line, _need_fft)
		p1_bits_res = log_search(_RE_P1_BITS, line, _need_p1_bits)
		ap1_bits_res = log_search(_RE_AP1_BITS, line, _need_ap1_bits)
		blocks_res = log_search(_RE_P2_BLOCKS, line, _need_p2_blocks)
		p2_res = log_search(_RE_P2_OK, line, _need_p2_ok)
		if res or ares:
			num = int(res.group(1) if res else ares.group(1))
			if num != p:
				if not found:
					adapter.debug("Looking for the exponent %s, but found %s", p, num)
				break
		if p2_res:
			found += 1
			if found == 1:
				if p2_res.group(3):
					iteration = int(p2_res.group(3))
					p2 = True
				else:
					iteration = int(p2_res.group(1))
					iterations = buffs = int(p2_res.group(2))
				stage = 2
		elif res and us_res and found < 20:
			found += 1
			aiteration = int(res.group(3))
			if found == 1:
				iteration = aiteration
				p1 = res.group(2) == "P1"
				if p1:
					stage = 1
			elif aiteration > iteration:
				break
			if not p1 and not (p2 or buffs):
				p1_res = log_search(_RE_P1_PIPE, line, _need_p1_pipe)
				p1 = res.group(2) == "OK" and bool(p1_res)
				if p1:
					stage = 1
			if len(list_usec_per_iter) < 5:
				list_usec_per_iter.append(int(us_res.group(1)))
		elif ares and found < 20:
			found += 1
			apercent = float(ares.group(2))
			if found == 1:
				percent = apercent
				p1 = True
				stage = 2
			elif apercent > percent:
				break
			if len(list_usec_per_iter) < 5:
				list_usec_per_iter.append(int(ares.group(4)))
		elif p2 and blocks_res:
			if not buffs:
				iterations = buffs = int(blocks_res.group(1))
				iteration -= int(blocks_res.group(2))
		elif p1 and (p1_bits_res or ap1_bits_res):
			if not bits:
				if p1_bits_res:
					iterations = bits = int(p1_bits_res.group(1))
					iteration = min(iteration, bits)
				else:
					iterations = bits = int(ap1_bits_res.group(2))
					iteration = int(bits * (percent / 100))
		elif fft_res and not fftlen:
			if int(fft_res.group(1)) != p:
				break
			fftlen = _input_unit(fft_res.group(2))
		if (buffs or (found == 20 and not p2 and (not p1 or bits))) and fftlen:
			break

	if not found:
		return (iteration, iterations, None, None, stage, fftlen), n_search
	msec_per_iter = median_low(list_usec_per_iter) / 1000 if list_usec_per_iter else None
	return (iteration, iterations, msec_per_iter, None, stage, fftlen), n_search


def _iter_corpus_files(argv_paths):
	if argv_paths:
		return [Path(p) for p in argv_paths]
	base = Path(r"C:\Users\jeffr\source\repos\logfiles")
	if not base.is_dir():
		raise SystemExit("Default log dir missing: {!r} (pass log paths as args)".format(str(base)))
	return sorted(base.glob("gpuowl*.log"))


def _run_accuracy(paths):
	cmd = [sys.executable, str(_REPO / "scripts" / "validate_gpuowl_log_guards.py")]
	cmd.extend(str(p) for p in paths)
	r = subprocess.run(cmd, cwd=str(_REPO), capture_output=True, text=True)
	if r.returncode != 0 and r.stdout:
		print(r.stdout, end="")
	if r.stderr:
		print(r.stderr, end="", file=sys.stderr)
	return r.returncode == 0


def main():
	ap = argparse.ArgumentParser(description=__doc__)
	ap.add_argument("log_paths", nargs="*", help="gpuowl logs (default: repos/logfiles/gpuowl*.log)")
	ap.add_argument("--repeat", type=int, default=5, help="timing repeats per mode (default 5)")
	ap.add_argument("--skip-accuracy", action="store_true")
	ap.add_argument(
		"--output",
		"-o",
		type=Path,
		default=_DEFAULT_RESULT_PATH,
		help="write result summary to this file (default: scripts/benchmark_gpuowl_log_guards.txt)",
	)
	args = ap.parse_args()

	paths = _iter_corpus_files(args.log_paths)
	if not paths:
		print("No log files.")
		return 1

	if not args.skip_accuracy:
		print("Accuracy (per-line eager == lazy for all patterns)...")
		if not _run_accuracy(paths):
			print("  FAIL: validate_gpuowl_log_guards.py\n")
			return 1
		print("  PASS\n")

	# Load all files once
	file_lines: list[tuple[Path, list[str], int]] = []
	for fp in paths:
		with open(fp, encoding="utf-8", errors="replace") as f:
			lines = f.readlines()
		p = _detect_p_from_log_end(lines)
		if p is None:
			print("Skip {!r}: could not detect exponent p from log tail.".format(fp.name))
			continue
		file_lines.append((fp, lines, p))

	if not file_lines:
		print("No files with detectable p.")
		return 1

	# Parse equivalence (single run each)
	mismatch = 0
	total_search_eager = total_search_guard = 0
	for fp, lines, p in file_lines:
		t_e, n_e = _parse_gpuowl_log_sim(lines, p, use_guards=False)
		t_g, n_g = _parse_gpuowl_log_sim(lines, p, use_guards=True)
		total_search_eager += n_e
		total_search_guard += n_g
		if t_e != t_g:
			mismatch += 1
			print("RESULT MISMATCH {!r} p={}: eager {} vs guarded {}".format(fp.name, p, t_e, t_g))

	if mismatch:
		print("\n{} file(s) differ guarded vs unguarded parse result.".format(mismatch))
		return 1
	print(
		"Parse result identical (guarded vs unguarded) for {} file(s).".format(len(file_lines))
	)
	print(
		"Total regex .search calls (sum over files, one parse each): eager {}  |  guarded {}  ({:.2f}% of eager)".format(
			total_search_eager,
			total_search_guard,
			100.0 * total_search_guard / total_search_eager if total_search_eager else 0.0,
		)
	)

	# Wall time: full corpus, many repeats
	def bench_corpus(use_guards: bool) -> float:
		t0 = time.perf_counter()
		for _ in range(args.repeat):
			for _fp, lines, p in file_lines:
				_parse_gpuowl_log_sim(lines, p, use_guards=use_guards)
		return time.perf_counter() - t0

	# Warmup
	bench_corpus(True)
	bench_corpus(False)

	times_e = []
	times_g = []
	for _ in range(3):
		times_e.append(bench_corpus(False))
		times_g.append(bench_corpus(True))

	best_e = min(times_e)
	best_g = min(times_g)
	print()
	print("Wall time, all files x {} repeats (lower is better):".format(args.repeat))
	print("  Unconditional .search: best of 3 outer: {:.3f} s  (mean {:.3f})".format(best_e, statistics.mean(times_e)))
	print("  Guarded .search:       best of 3 outer: {:.3f} s  (mean {:.3f})".format(best_g, statistics.mean(times_g)))
	speedup = best_e / best_g if best_g > 0 else None
	if speedup is not None:
		print("  Speedup (eager/guarded): {:.3f}x".format(speedup))
	print()
	py_ver = sys.version.split()[0]
	print("Python {}".format(py_ver))

	pct_guard = 100.0 * total_search_guard / total_search_eager if total_search_eager else 0.0
	accuracy_token = "SKIPPED" if args.skip_accuracy else "PASS"
	lines = [
		"mode=benchmark_gpuowl_log_guards",
		"time_iso={}".format(time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime())),
		"python={}".format(py_ver),
		"accuracy={}".format(accuracy_token),
		"repeat={}".format(args.repeat),
		"files={}".format(len(file_lines)),
		"total_search_eager={}".format(total_search_eager),
		"total_search_guard={}".format(total_search_guard),
		"pct_guard_of_eager={:.2f}".format(pct_guard),
		"wall_eager_best_s={:.6f}".format(best_e),
		"wall_eager_mean_s={:.6f}".format(statistics.mean(times_e)),
		"wall_guard_best_s={:.6f}".format(best_g),
		"wall_guard_mean_s={:.6f}".format(statistics.mean(times_g)),
	]
	if speedup is not None:
		lines.append("speedup_eager_over_guard={:.6f}".format(speedup))
	for fp, _lines, _p in file_lines:
		lines.append("corpus_file={}".format(fp.name))
	lines.extend(
		[
			"",
			"Parse result identical (guarded vs unguarded) for {} file(s).".format(len(file_lines)),
			"Total regex .search calls (sum over files, one parse each): eager {}  |  guarded {}  ({:.2f}% of eager)".format(
				total_search_eager,
				total_search_guard,
				pct_guard,
			),
			"",
			"Wall time, all files x {} repeats (lower is better):".format(args.repeat),
			"  Unconditional .search: best of 3 outer: {:.3f} s  (mean {:.3f})".format(
				best_e, statistics.mean(times_e)
			),
			"  Guarded .search:       best of 3 outer: {:.3f} s  (mean {:.3f})".format(
				best_g, statistics.mean(times_g)
			),
		]
	)
	if speedup is not None:
		lines.append("  Speedup (eager/guarded): {:.3f}x".format(speedup))
	lines.append("")
	lines.append("Python {}".format(py_ver))

	out_path = args.output.expanduser()
	out_path.parent.mkdir(parents=True, exist_ok=True)
	out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
	print("Wrote results to {!r}".format(str(out_path)))
	return 0


if __name__ == "__main__":
	sys.exit(main())
