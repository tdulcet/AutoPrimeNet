"""Validated form data and a noninteractive adapter for upstream registration.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import contextlib
import io
import json
import logging
import math


WORK_TYPES = {2: "Trial factoring", 3: "P−1 with bounds", 4: "P−1 factoring", 5: "ECM", 100: "LL", 101: "LL double-check", 150: "PRP", 151: "PRP double-check"}
DEFAULT_ENTRY = dict(work_type=150, exponent=0, sieve_depth=70, factor_to=72, pminus1ed=False, tests_saved=1.3, B1=100000, B2=10000000, curves=100, prp_base=3, prp_residue_type=1, known_factors=[])


def validate_shape(parameters):
	if not isinstance(parameters, dict) or set(parameters) != {"worker", "entries"}:
		raise ValueError("Choose a worker and an exponent batch.")
	worker, entries = parameters["worker"], parameters["entries"]
	if type(worker) is not int or not 1 <= worker <= 128 or not isinstance(entries, list) or not 1 <= len(entries) <= 100:
		raise ValueError("Select worker 1–128 and queue 1–100 exponents.")
	result = []
	for index, raw in enumerate(entries, 1):
		if not isinstance(raw, dict) or set(raw) - DEFAULT_ENTRY.keys():
			raise ValueError("Unsupported exponent parameters in row {}.".format(index))
		entry = DEFAULT_ENTRY | raw
		for key, low, high in (("work_type", 2, 151), ("exponent", 2, 10000000000), ("factor_to", 0, 99), ("B1", 100, None), ("B2", 0, None), ("curves", 1, None), ("prp_base", 2, None), ("prp_residue_type", 1, 5)):
			if type(entry[key]) is not int or entry[key] < low or high is not None and entry[key] > high or entry[key].bit_length() > 1024:
				raise ValueError("Row {}: invalid {}.".format(index, key))
		if entry["work_type"] not in WORK_TYPES or type(entry["pminus1ed"]) is not bool:
			raise ValueError("Row {}: select a supported work type and P−1 state.".format(index))
		for key, maximum in (("sieve_depth", 99), ("tests_saved", None)):
			try:
				valid = type(entry[key]) in (int, float) and math.isfinite(entry[key]) and entry[key] >= 0 and (maximum is None or entry[key] <= maximum)
			except OverflowError:
				valid = False
			if not valid:
				raise ValueError("Row {}: invalid {}.".format(index, key))
		if entry["work_type"] == 2 and (int(entry["sieve_depth"]) != entry["sieve_depth"] or entry["factor_to"] < entry["sieve_depth"]):
			raise ValueError("Trial factoring needs integer start bits and end bits at least as large.")
		factors = entry["known_factors"]
		if not isinstance(factors, list) or len(factors) > 32 or any(type(factor) is not int or factor < 2 or factor.bit_length() > 1024 for factor in factors):
			raise ValueError("Use at most 32 integer factors, each at most 1024 bits.")
		if factors and (entry["work_type"] in {100, 101} or entry["work_type"] == 151 and entry["prp_residue_type"] != 5):
			raise ValueError("This work type/residue mode does not accept known factors in the original registration workflow.")
		result.append(entry)
	if len({(row["work_type"], row["exponent"]) for row in result}) != len(result):
		raise ValueError("Remove duplicate work-type/exponent entries from the batch.")
	plan = {"worker": worker, "entries": result}
	if len(json.dumps(plan).encode("utf-8")) > 48 * 1024:
		raise ValueError("The exponent batch exceeds the 48 KiB registration limit.")
	return plan


def validate_plan(namespace, parameters):
	plan = validate_shape(parameters)
	if plan["worker"] > namespace["args"].num_workers:
		raise ValueError("The selected worker is not configured.")
	for row in plan["entries"]:
		p = row["exponent"]
		if not namespace["is_prime"](p):
			raise ValueError("Exponent {} is composite; there is no need to register it.".format(p))
		product = 1
		for factor in row["known_factors"]:
			product *= factor
			if not namespace["is_prime"](factor) or pow(2, p, product) != 1:
				raise ValueError("A supplied factor is composite or does not divide the specified Mersenne number with its multiplicity.")
	return plan


class FormAnswers:
	"""Only reviewed prompts have answers; unexpected/repeated prompts fail."""
	def __init__(self, plan):
		self.plan = plan
		self.index = 0
		self.factor_index = 0
		self.seen = set()

	@property
	def row(self):
		return self.plan["entries"][self.index]

	def integer(self, prompt, _default, amin=None, amax=None, base=0):
		if prompt.startswith("Known factor #"):
			factors = self.row["known_factors"]
			value = factors[self.factor_index] if self.factor_index < len(factors) else None
			self.factor_index += 1
			return value
		keys = {"Type of work": "work_type", "Exponent to test": "exponent", "Trial Factor (TF) starting bits": "sieve_depth", "Trial Factor (TF) ending bits": "factor_to", "PRP base": "prp_base", "PRP residue type": "prp_residue_type", "P-1 Bound #1": "B1", "P-1 Bound #2": "B2", "ECM Bound #1": "B1", "ECM Bound #2": "B2", "Curves to test": "curves"}
		value = self.plan["worker"] if prompt == "Worker number" else self.row[keys[prompt]] if prompt in keys else None
		if value is None or prompt in self.seen or amin is not None and value < amin or amax is not None and value > amax:
			raise ValueError("Unsupported or repeated backend integer prompt.")
		self.seen.add(prompt)
		return int(value)

	def decimal(self, prompt, _default, amin=None, amax=None):
		keys = {"Trial Factor (TF) bits": "sieve_depth", "Primality tests saved if factor is found": "tests_saved"}
		if prompt not in keys or prompt in self.seen:
			raise ValueError("Unsupported or repeated backend decimal prompt.")
		self.seen.add(prompt)
		value = self.row[keys[prompt]]
		if amin is not None and value < amin or amax is not None and value > amax:
			raise ValueError("Backend decimal input is outside its supported range.")
		return float(value)

	def boolean(self, prompt, _default):
		if prompt == "Has it been P-1 factored before?":
			return self.row["pminus1ed"]
		if prompt == "Do you want to register another exponent?":
			if self.index + 1 == len(self.plan["entries"]):
				return False
			self.index += 1
			self.factor_index = 0
			self.seen.clear()
			return True
		raise ValueError("Unsupported backend yes/no prompt.")


def install_answers(namespace, plan):
	answers = FormAnswers(plan)
	namespace.update(ask_int=answers.integer, ask_float=answers.decimal, ask_yn=answers.boolean, ask_ok_cancel=lambda: True)
	# Form values are explicit; no implicit mersenne.ca metadata request occurs.
	namespace["get_exponent"] = lambda *_: None
	block_terminal(namespace)


def block_terminal(namespace):
	def no_terminal(*_args, **_kwargs):
		raise ValueError("Unexpected terminal input in graphical registration.")
	namespace.update(input=no_terminal, ask_str=no_terminal, ask_pass=no_terminal, ask_ok=no_terminal)


def preview_plan(namespace, parameters, directory):
	plan = validate_plan(namespace, parameters)
	install_answers(namespace, plan)
	class Capture(io.StringIO):
		def close(self):
			pass
	buffer = Capture()
	def virtual_open(_path, mode, **_kwargs):
		if mode != "a":
			raise ValueError("Unexpected file access during registration preview.")
		return buffer
	namespace.update(open=virtual_open, LockFile=lambda *_: contextlib.nullcontext(), logger=logging.getLogger("gui_registration.preview"))
	namespace["read_workfile"] = lambda adapter, _path: (namespace["parse_assignment"](adapter, line) for line in buffer.getvalue().splitlines())
	namespace["register_assignments"] = lambda *_: False
	namespace["register_exponents"](namespace["config"], namespace["args"], [directory] * namespace["args"].num_workers)
	lines = buffer.getvalue().splitlines()
	if len(lines) != len(plan["entries"]):
		raise ValueError("The backend did not produce exactly one work line per requested exponent.")
	return {"plan": plan, "lines": lines, "network_enabled": False, "files_written": False, "server_confirmation": "unverified"}
