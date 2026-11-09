#!/usr/bin/env python3
"""Private live registration adapter; never imported by the GUI process.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import contextlib
import hashlib
import io
import json
import logging
from pathlib import Path
import sys

from gui_backend import _load_definitions, _read_source, _validate_config
from gui_config import ConfigDocument
from gui_mail_discovery import limit_lookup_responses
from gui_trace import debug_arguments
from gui_registration_plan import WORK_TYPES, block_terminal, install_answers, validate_plan, validate_shape


ROOT = Path(__file__).resolve().parent


def execute(request, before_main=None):
	"""Execute original startup, then supply graphical setup/exponent inputs."""
	if not isinstance(request, dict) or request.get("operation") not in {"register_computer", "register_exponents"}:
		raise ValueError("Unsupported graphical registration operation.")
	operation = request["operation"]
	parameters = request.get("parameters", {})
	if operation == "register_exponents":
		validate_shape(parameters)
	elif parameters:
		raise ValueError("Computer registration does not accept arbitrary parameters.")
	directory = Path(request["directory"]).expanduser().resolve()
	name = request["config_name"]
	if not isinstance(name, str) or not name or Path(name).name != name:
		raise ValueError("Select a configuration filename within the workspace.")
	document = ConfigDocument(str(directory), name)
	if document.bom:
		raise ValueError("The original CLI requires UTF-8 without BOM.")
	data = document.data
	if hashlib.sha256(data).hexdigest() != request["config_sha256"]:
		raise ValueError("Configuration changed before registration startup.")
	path = ROOT / "autoprimenet.py"
	argv = sys.argv
	sys.argv = [str(path), "--workdir", str(directory), "--config-file", name, "--timeout", "0", *debug_arguments(document.config)]
	if operation == "register_exponents":
		sys.argv.append("--register-exponents")
	try:
		# Original argv/config/proxy/encryption/logging/locking initialization is
		# preserved. Only the final main call is deferred until inputs are bound.
		namespace = _load_definitions(path)
		namespace["initialize_cli"]()
		if operation == "register_exponents":
			if not namespace["get_guid"](namespace["config"]):
				raise ValueError("Register the computer before registering exponents.")
			plan = validate_plan(namespace, parameters)
			install_answers(namespace, plan)
		else:
			# Skip the terminal setup initializer, but reuse main's normal setup
			# completion, option merging and register_instance/program_options.
			namespace["args"].setup = True
			namespace["test_email"] = False
			block_terminal(namespace)
		if before_main is not None:
			before_main(namespace)  # Injection is available only to isolated tests.
		namespace["main"]()
	except SystemExit as error:
		return int(error.code or 0)
	finally:
		sys.argv = argv
	return 0


def lookup_exponent(request):
	"""Read registration suggestions without startup, workspace writes or reservation."""
	exponent, kind = request["exponent"], request["work_type"]
	if type(exponent) is not int or not 2 <= exponent <= 10000000000 or type(kind) is not int or kind not in WORK_TYPES:
		raise ValueError("Invalid exponent or work type.")
	document = ConfigDocument(request["directory"], request["config_name"])
	if hashlib.sha256(document.data).hexdigest() != request["config_sha256"]:
		raise ValueError("Configuration changed before exponent lookup.")
	path = ROOT / "autoprimenet.py"
	_, tree, boundary = _read_source(path)
	namespace = _load_definitions(path, tree, boundary)
	try:
		if not namespace["is_prime"](exponent):
			raise ValueError("Choose a prime exponent.")
		_validate_config(namespace, tree, boundary, {"text": document.text, "directory": str(document.directory), "config_name": document.path.name})
		args = namespace["args"]
		namespace["configure_proxy"](args)
		namespace["TIMEOUT"] = 8
		limit_lookup_responses(namespace)
		result = namespace["get_exponent"](args, logging.getLogger("gui_registration.lookup"), exponent)
		if ConfigDocument(str(document.directory), document.path.name).version != document.version:
			raise ValueError("Configuration changed during exponent lookup.")
		metadata = namespace["exponent_registration_metadata"](result, exponent)
		if metadata is None:
			return None
		depth, bound1, bound2, ecm_b1, ecm_b2, factors = metadata
		if not 0 <= depth <= 99 or len(factors) > 32 or any(factor < 2 or factor.bit_length() > 1024 for factor in factors):
			raise ValueError("Exponent metadata exceeds GUI limits.")
		factored = bool(bound1) and bool(bound2)
		suggestions = dict(sieve_depth=depth, pminus1ed=factored, tests_saved=0.0 if factored else 1.3, known_factors=factors)
		if kind == 2:
			suggestions["factor_to"] = min(99, max(namespace["factor_limit"](exponent), depth + 1))
		elif kind == 5:
			suggestions.update(B1=int(ecm_b1) or 250000, B2=int(ecm_b2), curves=100)
		elif kind == 3 or args.gpuowl and kind in {4, 150, 151}:
			_, (b1, b2), _ = namespace["walk"](exponent, depth)
			suggestions.update(B1=b1, B2=b2)
		return suggestions
	finally:
		namespace["session"].close()


def main():
	try:
		data = sys.stdin.buffer.read(65537)
		if len(data) > 65536:
			raise ValueError("Registration request is too large.")
		request = json.loads(data)
		if isinstance(request, dict) and request.get("operation") == "lookup_exponent":
			with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
				suggestions = lookup_exponent(request)
			print(json.dumps({"suggestions": suggestions}))
			return 0
		return execute(request)
	except Exception:
		# No raw request/configuration data is emitted by the adapter.
		print("Graphical registration failed; inspect the AutoPrimeNet log and refresh the workspace.", file=sys.stderr)
		return 1


if __name__ == "__main__":
	sys.exit(main())
