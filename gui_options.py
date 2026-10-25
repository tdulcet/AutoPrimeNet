"""Typed metadata and validation for the first graphical configuration forms.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from dataclasses import dataclass
import math
from pathlib import Path


@dataclass(frozen=True)
class Field:
	key: str
	label: str
	tab: str
	default: str = ""
	kind: str = "text"
	minimum: float | None = None
	maximum: float | None = None


FIELDS = (
	Field("username", "GIMPS username (or ANONYMOUS)", "PrimeNet"),
	Field("ComputerID", "Computer name (optional)", "PrimeNet"),
	Field("HoursBetweenCheckins", "Progress check-in interval (hours)", "PrimeNet", "1", "integer", 1, 168),
	Field("CPUHours", "Expected computation hours per day", "PrimeNet", "24", "integer", 1, 24),
	Field("DaysOfWork", "Days of work to queue", "Assignments", "", "decimal", 0, 180),
	Field("num_cache", "Legacy extra assignment cache", "Assignments", "0", "integer", 0),
	Field("work_file", "Work filename", "Settings", "worktodo.txt", "filename"),
	Field("results_file", "Results filename (blank: program default)", "Settings", "", "filename"),
	Field("logfile", "Activity log path", "Settings", "autoprimenet.log"),
	Field("ProofArchiveDir", "Proof archive directory (optional)", "Settings"),
	Field("GetMinExponent", "Minimum assignment exponent", "Advanced", "", "integer", 2, 9999999999),
	Field("GetMaxExponent", "Maximum assignment exponent", "Advanced", "", "integer", 2, 9999999999),
	Field("CertWork", "Receive certification work (PRPLL only)", "Advanced", "", "boolean"),
	Field("CertDailyCPULimit", "Certification time limit (%)", "Advanced", "10", "integer", 1, 100),
)


def validate_fields(values):
	"""Reject malformed graphical input before passing it to the backend."""
	result = {}
	for field in FIELDS:
		value = str(values.get(field.key, field.default)).strip()
		if "\n" in value or "\r" in value or "\x00" in value:
			raise ValueError(field.label + ": enter a single-line value.")
		if field.key in {"username", "ComputerID"} and len(value) > 20:
			raise ValueError(field.label + ": maximum 20 characters.")
		if field.key == "username" and not value:
			raise ValueError("A GIMPS username or ANONYMOUS is required.")
		if value and field.kind in {"integer", "decimal"}:
			try:
				number = int(value) if field.kind == "integer" else float(value)
			except ValueError as error:
				raise ValueError(field.label + ": enter a valid number.") from error
			if (isinstance(number, float) and not math.isfinite(number)) or (field.minimum is not None and number < field.minimum) or (field.maximum is not None and number > field.maximum):
				raise ValueError(field.label + ": value is outside the supported range.")
		if value and field.kind == "filename" and (Path(value).name != value or value in {".", ".."}):
			raise ValueError(field.label + ": enter a filename without a directory.")
		if field.kind == "boolean" and value not in {"", "True", "False"}:
			raise ValueError(field.label + ": choose inherit, True or False.")
		result[field.key] = value or None
	return result
