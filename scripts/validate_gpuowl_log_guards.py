#!/usr/bin/env python3
"""Verify GpuOwl log guards: lazy .search == eager .search per line/pattern.

Guard implementations MUST match autoprimenet._gpuowl_log_need_* and GPUOWL_LOG_* patterns.

Default corpus: ../logfiles/gpuowl*.log (see DEFAULT_LOGFILES_DIR at top of script).
Override: python scripts/validate_gpuowl_log_guards.py path1 path2 ...

Exit 0 if all lines pass; exit 1 on first mismatch.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Configuration — default corpus when no paths are passed on the command line.
# ---------------------------------------------------------------------------
DEFAULT_LOGFILES_DIR: Path = _REPO.parent / "logfiles"
DEFAULT_CORPUS_GLOB = "gpuowl*.log"
# ---------------------------------------------------------------------------

# --- SYNC: autoprimenet.GPUOWL_LOG_MAIN_LINE_GUARD_RE + _gpuowl_log_need_* ---
_GPUOWL_LOG_MAIN_LINE_GUARD_RE = re.compile(r"\d{6,}.*\d{4,}")


def need_main_search(line: str) -> bool:
	return _GPUOWL_LOG_MAIN_LINE_GUARD_RE.search(line) is not None


def need_ap1_search(line: str) -> bool:
	i = line.find("P1 ")
	if i < 1 or not line[i - 1].isdigit():
		return False
	j = i - 1
	while j >= 0 and line[j].isdigit():
		j -= 1
	return i - 1 - j >= 6


def need_us_per_search(line: str) -> bool:
	return " us/it" in line


def need_fft_search(line: str) -> bool:
	return " FFT:" in line


def need_p1_bits_search(line: str) -> bool:
	return (" bits" in line or "bits;" in line) and (" P1" in line or "P1(" in line)


def need_ap1_bits_search(line: str) -> bool:
	return "P1" in line and "%" in line and "B1(" in line


def need_p2_blocks_search(line: str) -> bool:
	return "blocks:" in line and "P2(" in line


def need_p2_ok_search(line: str) -> bool:
	return " P2(" in line or ("/" in line and " P2 " in line)


def need_p1_pipe_search(line: str) -> bool:
	return "| P1(" in line


# --- SYNC: autoprimenet.GPUOWL_LOG_* ---
_GPUOWL_LINE_PATTERNS = (
	("MAIN", re.compile(r"([0-9]{6,}) (LL|P1|OK|EE)? +([0-9]{4,})"), need_main_search),
	(
		"AP1",
		re.compile(r"([0-9]{6,})P1 +([0-9]+\.[0-9]+)% ([KE])? +[0-9a-f]{16} +([0-9]+)"),
		need_ap1_search,
	),
	("US_PER", re.compile(r"\b([0-9]+) us/it;?"), need_us_per_search),
	("FFT", re.compile(r"\b([0-9]{6,}) FFT: ([0-9]+(?:\.[0-9]+)?[KM])\b"), need_fft_search),
	(
		"P1_BITS",
		re.compile(
			r"\b[0-9]{6,} P1(?: B1=[0-9]+, B2=[0-9]+;|\([0-9]+(?:\.[0-9])?M?\)) ([0-9]+) bits;?\b"
		),
		need_p1_bits_search,
	),
	(
		"AP1_BITS",
		re.compile(r"\b[0-9]{6,}P1 +[0-9]+\.[0-9]+% @([0-9]+)/([0-9]+) B1\([0-9]+\)"),
		need_ap1_bits_search,
	),
	(
		"P2_BLOCKS",
		re.compile(
			r"[0-9]{6,} P2\([0-9]+(?:\.[0-9])?M?,[0-9]+(?:\.[0-9])?M?\) ([0-9]+) blocks: ([0-9]+) - ([0-9]+);"
		),
		need_p2_blocks_search,
	),
	(
		"P2_OK",
		re.compile(
			r"[0-9]{6,} P2(?: ([0-9]+)/([0-9]+)|\([0-9]+(?:\.[0-9])?M?,[0-9]+(?:\.[0-9])?M?\) OK @([0-9]+)):"
		),
		need_p2_ok_search,
	),
	("P1_PIPE", re.compile(r"\| P1\([0-9]+(?:\.[0-9])?M?\)"), need_p1_pipe_search),
)


def _match_equal(a, b):
	if a is None and b is None:
		return True
	if a is None or b is None:
		return False
	return a.group(0) == b.group(0) and a.span() == b.span()


def _iter_corpus_files(argv):
	if argv:
		return [Path(p) for p in argv]
	base = DEFAULT_LOGFILES_DIR
	if not base.is_dir():
		raise SystemExit("Default log dir missing: {!r} (pass log paths as args)".format(str(base)))
	return sorted(base.glob(DEFAULT_CORPUS_GLOB))


def main():
	paths = _iter_corpus_files(sys.argv[1:])
	if not paths:
		print("No log files to scan.")
		return 0
	total_lines = 0
	for fp in paths:
		with open(fp, encoding="utf-8", errors="replace") as f:
			for lineno, line in enumerate(f, start=1):
				total_lines += 1
				for name, pat, need in _GPUOWL_LINE_PATTERNS:
					eager = pat.search(line)
					lazy = pat.search(line) if need(line) else None
					if not _match_equal(eager, lazy):
						print("MISMATCH {!r} line {} pattern {}:".format(fp.name, lineno, name))
						print(line[:200].rstrip())
						print("  eager: {!r}".format(eager.group(0) if eager else None))
						print("  lazy:  {!r}".format(lazy.group(0) if lazy else None))
						return 1
	print(
		"OK: {} lines across {} files; eager == lazy for all {} patterns.".format(
			total_lines, len(paths), len(_GPUOWL_LINE_PATTERNS)
		)
	)
	return 0


if __name__ == "__main__":
	sys.exit(main())
