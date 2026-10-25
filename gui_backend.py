#!/usr/bin/env python3
"""Offline integration bridge for the optional AutoPrimeNet GUI.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only

Run as a private child process, never import AutoPrimeNet into the GUI process.
This bridge has no command that can change assignments or contact a server.
"""

import sys

if sys.version_info < (3, 15):
	if __name__ == "__main__":
		print("AutoPrimeNet GUI requires Python 3.15.0 or later.", file=sys.stderr)
		sys.exit(2)
	raise ImportError("AutoPrimeNet GUI requires Python 3.15.0 or later.")

import argparse
import ast
import contextlib
from configparser import ConfigParser
import hashlib
import io
import json
import logging
from pathlib import Path


# Deliberately fail closed when the audited upstream implementation changes.
# Updating this value requires a fresh integration review, not just rehashing.
AUDITED_SOURCE_SHA256 = "05776d74b7b816c52774c30de438e7dcf047127a810daa8ee36335f8b8e7ec12"
MAX_REQUEST_BYTES = 1024 * 1024
PROTOCOL_VERSION = 1


class BackendError(Exception):
	"""A safe, user-facing error from the offline bridge."""


def _assignment_target(node, name):
	return isinstance(node, ast.Assign) and any(
		isinstance(target, ast.Name) and target.id == name for target in node.targets
	)


def _read_source(path):
	source = path.read_bytes()
	if hashlib.sha256(source).hexdigest() != AUDITED_SOURCE_SHA256:
		raise BackendError("AutoPrimeNet source differs from the audited version; integration review required.")
	tree = ast.parse(source, filename=str(path))
	boundaries = [index for index, node in enumerate(tree.body) if _assignment_target(node, "parser")]
	if len(boundaries) != 1:
		raise BackendError("Unsupported AutoPrimeNet startup layout.")
	boundary = boundaries[0]
	return source, tree, boundary


def _network_guard(event, _args):
	"""Deny outbound Python socket operations for the entire prototype child."""
	if event in {"socket.connect", "socket.getaddrinfo", "socket.sendto"}:
		raise BackendError("Network access is disabled in the offline GUI prototype.")


def _load_definitions(path, tree, boundary):
	# Only the reviewed prefix is executed: no argv parsing, config merge, instance
	# lock, logfile, setup or main(). Native capability/session initialization does
	# occur, which is why this namespace belongs in a short-lived private child.
	module = ast.Module(body=tree.body[:boundary], type_ignores=[])
	namespace = {"__name__": "_autoprimenet_gui_backend", "__file__": str(path)}
	exec(compile(module, str(path), "exec"), namespace)  # noqa: S102
	if not all(callable(namespace.get(name)) for name in ("Assignment", "parse_assignment", "output_assignment")):
		raise BackendError("Required AutoPrimeNet assignment helpers are unavailable.")
	return namespace


def _parser_inventory(tree):
	options = []
	for node in sorted(ast.walk(tree), key=lambda item: getattr(item, "lineno", 0)):
		if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute):
			continue
		if node.func.attr != "add_argument":
			continue
		flags = [item.value for item in node.args if isinstance(item, ast.Constant) and isinstance(item.value, str)]
		keywords = {item.arg: item.value for item in node.keywords}
		canonical = next((flag for flag in flags if flag.startswith("--")), flags[0])
		dest = ast.literal_eval(keywords["dest"]) if "dest" in keywords else canonical.lstrip("-").replace("-", "_")
		options.append({"flags": flags, "dest": dest, "source_line": node.lineno})
	# argparse creates help without an explicit add_argument call.
	options.append({"flags": ["-h", "--help"], "dest": "help", "source_line": None})
	return options


def _parse_work(namespace, lines):
	if not isinstance(lines, list) or len(lines) > 1000 or any(not isinstance(line, str) for line in lines):
		raise BackendError("Work preview requires a list of at most 1000 text lines.")
	if any("\n" in line or "\r" in line for line in lines):
		raise BackendError("Each work preview entry must be a single line.")
	logger = logging.LoggerAdapter(logging.getLogger("gui_backend.preview"), {})
	results = []
	for line in lines:
		assignment = namespace["parse_assignment"](logger, line)
		if assignment is None:
			results.append({"parsed": False})
			continue
		results.append({
			"parsed": True,
			"fields": {name: getattr(assignment, name) for name in assignment.__slots__},
			"canonical": namespace["output_assignment"](assignment),
			"server_confirmation": "unverified",
		})
	return {"assignments": results, "validation": "format parsing only; no server reservation or mathematical validation"}


def _validate_config(namespace, tree, boundary, request):
	"""Initialize parser/configuration in memory; never execute CLI startup."""
	text = request.get("text")
	directory = request.get("directory")
	name = request.get("config_name", "prime.ini")
	if not isinstance(text, str) or not isinstance(directory, str) or not isinstance(name, str):
		raise BackendError("Configuration validation requires text, a working directory and filename.")
	if not name or Path(name).name != name or not Path(directory).is_dir():
		raise BackendError("Select an existing working directory and a configuration filename without a path.")
	end = next(index for index in range(boundary, len(tree.body)) if _assignment_target(tree.body[index], "args"))
	exec(compile(ast.Module(body=tree.body[boundary:end], type_ignores=[]), namespace["__file__"], "exec"), namespace)  # noqa: S102
	parser = namespace["parser"]
	arguments = ["--workdir", directory, "--config-file", name]
	args = parser.parse_args(arguments)
	explicit = namespace["argparse"].Namespace(**dict.fromkeys(vars(args)))
	parser.parse_args(arguments, namespace=explicit)
	namespace["args_no_defaults"] = namespace["argparse"].Namespace(**{key: value for key, value in vars(explicit).items() if value is not None})
	namespace["args"] = args
	namespace["workdir"] = directory
	# Direct dictionary lookup can expose unresolved lazy-import bindings in
	# Python 3.15; use the standard-library parser imported by this bridge.
	config = ConfigParser()
	config.optionxform = str
	config.read_string(text)
	for section in ("PrimeNet", "Email", "Internals"):
		if not config.has_section(section):
			config.add_section(section)
	namespace["config"] = config
	namespace["merge_config_and_options"](config, args)
	# The upstream CLI does not persist --timeout. Keep the GUI's preference
	# in its own section and pass it explicitly to the owned native runtime.
	args.timeout = config.getint("GUI", "PollSeconds", fallback=3600)
	from gui_trace import debug_level
	args.debug = debug_level(config)
	# Work on a private in-memory config: decryption may update its keys/GUID.
	# No plaintext or encrypted credential is returned in the result.
	namespace["decrypt"](config, args)
	args.work_preference = args.work_preference or [12 if args.mfaktc or args.mfakto or args.primepath else 101 if args.cudalucas else 150]
	if args.results_file is None:
		args.results_file = "results.json.txt" if args.mfaktc or args.mfakto or args.primepath else "results.txt"
	if args.days_of_work is None:
		args.days_of_work = 1.0 if args.mfaktc or args.mfakto or args.primepath else 3.0
	for variable in ("RE", "PROGRAM", "SUPPORTED"):
		node = next(item for item in tree.body if _assignment_target(item, variable))
		exec(compile(ast.Module(body=[node], type_ignores=[]), namespace["__file__"], "exec"), namespace)  # noqa: S102

	def reject(message):
		# Most parser errors identify fields/ranges. Redact any configured secret
		# before making the explanation available to the GUI status line.
		for attr in ("password", "proxy_password", "email_password"):
			secret = getattr(args, attr, None)
			if secret:
				message = message.replace(secret, "[redacted]")
		raise BackendError(message)

	parser.error = reject
	namespace["check_options"](parser, args)
	for attribute in ("work_file", "results_file", "logfile", "archive_dir"):
		value = getattr(args, attribute, None)
		if value and Path(value).name.casefold() in {"~lock", "~gui-monitor.lock", ".gui-runner.guard"}:
			raise BackendError("Work/results/log/archive paths must not use reserved instance-lock filenames.")
	if not 1 <= args.num_workers <= 128:
		raise BackendError("GUI configuration supports 1–128 workers.")
	if args.timeout < 0 or 0 < args.timeout < 1800 or args.timeout > args.hours_between_checkins * 3600:
		raise BackendError("Update interval must be 0 or at least 1800 seconds and no greater than the check-in interval.")
	directories = [str((Path(directory) / item).resolve()) for item in args.dirs] if args.dirs else [str(Path(directory).resolve())]
	if any(not Path(item).is_dir() for item in directories):
		raise BackendError("A configured worker directory does not exist.")
	if not args.prpll and len(directories) != len(set(directories)):
		raise BackendError("Worker directories resolve to the same location.")
	return {
		"program": namespace["PROGRAM"]["name"], "num_workers": args.num_workers,
		"work_preferences": args.work_preference, "supported_preferences": sorted(namespace["SUPPORTED"]),
		"results_file": args.results_file, "days_of_work": args.days_of_work,
		"timeout": args.timeout, "checkin_hours": args.hours_between_checkins,
		"watch": args.watch is not False, "debug_level": args.debug, "require_lock": args.lock is not False,
		"network_enabled": False, "configuration_written": False,
	}


def _protect_credentials(namespace, tree, boundary, request):
	"""Encrypt only explicit replacements with the original CLI implementation."""
	replacements = request.get("credentials")
	if not isinstance(replacements, dict) or not replacements or set(replacements) - {"proxy", "email"}:
		raise BackendError("Select a supported password to replace.")
	if any(not isinstance(value, str) or not value or len(value) > 4096 or any(char in value for char in "\r\n\x00") for value in replacements.values()):
		raise BackendError("Passwords must contain 1–4096 characters without line breaks or NUL.")
	_validate_config(namespace, tree, boundary, request)
	args, config = namespace["args"], namespace["config"]
	if args.encrypt is False:
		raise BackendError("Enable password encryption or clear its override before replacing a password.")
	if not namespace["libcrypto"]:
		raise BackendError("OpenSSL encryption is unavailable; no password was saved.")
	mapping = {"proxy": ("PrimeNet", "ProxyPass", "proxy_password"), "email": ("Email", "password", "email_password")}
	# Avoid opportunistically re-encrypting unrelated credentials. The isolated
	# namespace is discarded after this request; no upstream files are written.
	namespace["OPTIONS_ENCRYPT"] = {}
	for key, secret in replacements.items():
		section, option, attribute = mapping[key]
		config.set(section, option, secret.replace("%", "%%"))
		setattr(args, attribute, secret)
		namespace["OPTIONS_ENCRYPT"].setdefault(section, {})[attribute] = option
	namespace["check_options"](namespace["parser"], args)
	args.encrypt = True
	try:
		namespace["encrypt"](config, args)
	except (Exception, SystemExit) as error:
		raise BackendError("Password encryption failed; no password was saved.") from error
	protected = {}
	for key in replacements:
		section, option, _ = mapping[key]
		encrypted = "encrypted_" + option
		if config.has_option(section, option) or not config.has_option(section, encrypted):
			raise BackendError("Password encryption failed; no password was saved.")
		protected[key] = config.get(section, encrypted)
	return {"credentials": protected, "hardware_guid": config.get("PrimeNet", "HardwareGUID"), "network_enabled": False}


def _dispatch(request, path):
	if not isinstance(request, dict) or request.get("protocol") != PROTOCOL_VERSION:
		raise BackendError("Unsupported GUI backend protocol.")
	operation = request.get("operation")
	if operation not in {"capabilities", "parse_work", "validate_config", "protect_credentials", "preview_registration", "debug_report", "cli_help", "discover_gpus"}:
		raise BackendError("Unsupported offline bridge operation.")
	_source, tree, boundary = _read_source(path)
	if operation == "capabilities":
		return {
			"backend_version": ast.literal_eval(next(node.value for node in tree.body if _assignment_target(node, "VERSION"))),
			"source_sha256": AUDITED_SOURCE_SHA256,
			"operations": ["capabilities", "parse_work", "validate_config", "protect_credentials", "preview_registration", "debug_report", "cli_help", "discover_gpus"],
			"network_enabled": False,
			"cli_options": _parser_inventory(tree),
		}
	# Reject invalid request shape before initializing the upstream prefix.
	lines = request.get("lines")
	if operation == "parse_work" and (not isinstance(lines, list) or len(lines) > 1000 or any(not isinstance(line, str) for line in lines)):
		raise BackendError("Work preview requires a list of at most 1000 text lines.")
	namespace = _load_definitions(path, tree, boundary)
	try:
		if operation == "discover_gpus":
			from gui_hardware import gpu_settings
			devices = []
			for record in namespace["get_gpus"]():
				try:
					settings = gpu_settings(record)
				except ValueError:
					continue
				devices.append({"name": record[0], "source": record[7], "settings": settings})
			return {"devices": devices, "network_enabled": False, "files_written": False}
		if operation == "cli_help":
			end = next(index for index in range(boundary, len(tree.body)) if _assignment_target(tree.body[index], "args"))
			exec(compile(ast.Module(body=tree.body[boundary:end], type_ignores=[]), str(path), "exec"), namespace)
			namespace["parser"].prog = path.name
			return {"text": namespace["parser"].format_help(), "network_enabled": False, "files_written": False}
		if operation == "debug_report":
			_validate_config(namespace, tree, boundary, request)
			buffer = io.StringIO()
			with contextlib.redirect_stdout(buffer):
				namespace["debug_info"](namespace["config"], namespace["args"])
			text = buffer.getvalue()
			for attribute in ("password", "proxy_password", "email_password"):
				secret = getattr(namespace["args"], attribute, None)
				if secret:
					text = text.replace(secret, "[redacted]")
			if len(text.encode("utf-8")) > 256 * 1024:
				raise BackendError("The diagnostic report exceeds the 256 KiB limit.")
			return {"text": text, "private": True, "network_enabled": False, "files_written": False}
		if operation == "preview_registration":
			from gui_registration_plan import preview_plan
			_validate_config(namespace, tree, boundary, request)
			try:
				return preview_plan(namespace, request.get("parameters"), request["directory"])
			except ValueError as error:
				raise BackendError(str(error)) from error
		if operation == "protect_credentials":
			return _protect_credentials(namespace, tree, boundary, request)
		if operation == "validate_config":
			return _validate_config(namespace, tree, boundary, request)
		return _parse_work(namespace, lines)
	finally:
		# The upstream prefix registers this close at exit as well. Requests close
		# is idempotent; explicitly release it after this single preview operation.
		namespace["session"].close()


def main():
	parser = argparse.ArgumentParser(description=__doc__)
	parser.add_argument("--source", type=Path, default=Path(__file__).with_name("autoprimenet.py"))
	args = parser.parse_args()
	sys.addaudithook(_network_guard)
	try:
		data = sys.stdin.buffer.read(MAX_REQUEST_BYTES + 1)
		if len(data) > MAX_REQUEST_BYTES:
			raise BackendError("GUI backend request exceeds the size limit.")
		request = json.loads(data)
		# Upstream initialization diagnostics must never corrupt the JSON channel
		# or leak request contents. This prototype reports sanitized errors only.
		with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
			result = _dispatch(request, args.source)
		response = {"protocol": PROTOCOL_VERSION, "ok": True, "result": result}
		exit_code = 0
	except BackendError as error:
		response = {"protocol": PROTOCOL_VERSION, "ok": False, "error": str(error)}
		exit_code = 1
	except (Exception, SystemExit):
		response = {"protocol": PROTOCOL_VERSION, "ok": False, "error": "Offline backend failed; check source and environment dependencies."}
		exit_code = 1
	print(json.dumps(response, ensure_ascii=True))
	return exit_code


if __name__ == "__main__":
	sys.exit(main())
