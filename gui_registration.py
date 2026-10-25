#!/usr/bin/env python3
"""Private live registration adapter; never imported by the GUI process.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import ast
import hashlib
import json
from pathlib import Path
import sys

from gui_backend import _read_source
from gui_config import ConfigDocument
from gui_registration_plan import block_terminal, install_answers, validate_plan, validate_shape


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
	_source, tree, _boundary = _read_source(path)
	main_calls = [index for index, node in enumerate(tree.body) if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "main"]
	if len(main_calls) != 1:
		raise ValueError("Unsupported AutoPrimeNet main entry point.")
	argv = sys.argv
	sys.argv = [str(path), "--workdir", str(directory), "--config-file", name, "--timeout", "0"]
	if operation == "register_exponents":
		sys.argv.append("--register-exponents")
	namespace = {"__name__": "__main__", "__file__": str(path)}
	try:
		# Original argv/config/proxy/encryption/logging/locking initialization is
		# preserved. Only the final main call is deferred until inputs are bound.
		exec(compile(ast.Module(body=tree.body[:main_calls[0]], type_ignores=[]), str(path), "exec"), namespace)
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


def main():
	try:
		data = sys.stdin.buffer.read(65537)
		if len(data) > 65536:
			raise ValueError("Registration request is too large.")
		return execute(json.loads(data))
	except Exception:
		# No raw request/configuration data is emitted by the adapter.
		print("Graphical registration failed; inspect the AutoPrimeNet log and refresh the workspace.", file=sys.stderr)
		return 1


if __name__ == "__main__":
	sys.exit(main())
