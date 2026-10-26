"""Translate the original GPU discovery records into reviewed form overrides.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import math


def gpu_settings(record):
	"""Match original setup's GPU overrides, retaining unknown cores/caches."""
	if not isinstance(record, (list, tuple)) or len(record) != 8:
		raise ValueError("Unsupported GPU discovery record.")
	name, cores, frequency, l1, l2, memory, features, source = record
	if any(not isinstance(value, str) or len(value) > 4096 or any(char in value for char in "\r\n\x00") for value in (name, features, source)):
		raise ValueError("Invalid GPU description.")
	for value in (cores, frequency, l1, l2, memory):
		if value is None:
			continue
		if isinstance(value, bool) or not isinstance(value, (int, float)):
			raise ValueError("Invalid GPU hardware measurement.")
		try:
			valid = math.isfinite(value) and 0 <= value <= 2 ** 53 and value == int(value)
		except OverflowError:
			valid = False
		if not valid:
			raise ValueError("Invalid GPU hardware measurement.")
	if frequency is None or memory is None:
		raise ValueError("GPU frequency or memory is unavailable.")
	values = {"CpuBrand": name, "cpu_features": features, "CpuSpeed": str(int(frequency)), "memory": str(int(memory)), "Memory": str(round(memory * 0.9))}
	if cores:
		values.update(NumCores=str(int(cores)), CpuNumHyperthreads="1")
	if l1 and l2:
		values.update(L1=str(int(l1)), L2=str(int(l2)), L3="0")
	return values
