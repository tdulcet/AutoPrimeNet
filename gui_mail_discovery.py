#!/usr/bin/env python3
"""Explicit network-enabled SMTP discovery, isolated from the offline bridge.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import ast
import contextlib
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys

from gui_backend import _assignment_target, _load_definitions, _read_source, _validate_config

ROOT = Path(__file__).resolve().parent
MAX_BYTES = 16384


def mail_settings(record):
	"""Validate provider data before offering explicit form overrides."""
	if not isinstance(record, (tuple, list)) or len(record) != 5:
		raise ValueError("Unsupported mail-provider response.")
	label, host, port, security, username = record
	if not isinstance(host, str) or not host or len(host) > 253 or any(ord(char) < 33 or ord(char) == 127 or char in "/\\@?#" for char in host):
		raise ValueError("Invalid mail-provider hostname.")
	if type(port) is not int or not 1 <= port <= 65535:
		raise ValueError("Invalid mail-provider port.")
	if not isinstance(security, str) or security not in {"SSL", "STARTTLS", "plain"}:
		raise ValueError("The provider returned an unknown connection-security mode; configure SMTP manually.")
	for value in (label, username):
		if value is not None and (not isinstance(value, str) or len(value) > 512 or any(ord(char) < 32 or ord(char) == 127 for char in value)):
			raise ValueError("Invalid mail-provider description.")
	values = {"smtp_server": f"{host}:{port}", "tls": str(security == "SSL"), "starttls": str(security == "STARTTLS")}
	if username is not None:
		values["email_username"] = username
	return {"provider": label or host, "security": security, "settings": values}


def execute(request, before_discovery=None):
	"""Read saved proxy policy; call only original provider discovery, never main."""
	from gui_config import ConfigDocument
	if not isinstance(request, dict) or request.get("protocol") != 1 or request.get("operation") != "discover_mail":
		raise ValueError("Unsupported mail discovery request.")
	email = request.get("email")
	if not isinstance(email, str) or len(email) > 254 or any(ord(char) < 32 for char in email):
		raise ValueError("Enter a single sender email address.")
	document = ConfigDocument(request["directory"], request["config_name"])
	if hashlib.sha256(document.data).hexdigest() != request.get("config_sha256"):
		raise ValueError("Configuration changed; refresh before mail discovery.")
	path = ROOT / "autoprimenet.py"
	_source, tree, boundary = _read_source(path)
	namespace = _load_definitions(path, tree, boundary)
	try:
		if not namespace["EMAIL_RE"].fullmatch(email):
			raise ValueError("Enter a valid sender email address.")
		_validate_config(namespace, tree, boundary, {"text": document.text, "directory": str(document.directory), "config_name": document.path.name})
		# Reuse only the audited proxy initialization statements. Skip all native
		# startup, lock files, logs, setup, scheduler and email sending.
		index = next(i for i, node in enumerate(tree.body) if _assignment_target(node, "PROXIES"))
		proxy_if = tree.body[index + 1]
		if not isinstance(proxy_if, ast.If) or ast.unparse(proxy_if.test) != "args.proxy":
			raise ValueError("Unsupported proxy startup layout.")
		exec(compile(ast.Module(body=tree.body[index:index + 2], type_ignores=[]), str(path), "exec"), namespace)
		namespace["TIMEOUT"] = 8
		if before_discovery is not None:
			before_discovery(namespace)  # Test injection is not part of JSON IPC.
		record = namespace["email_autoconfig"](namespace["args"], email)
		result = mail_settings(record) if record is not None else None
		if ConfigDocument(str(document.directory), document.path.name).version != document.version:
			raise ValueError("Configuration changed during discovery; refresh and retry.")
		return {"match": result, "network_enabled": True, "files_written": False, "email_sent": False}
	finally:
		namespace["session"].close()


def discover_mail(document, email):
	"""Bound the entire lookup and keep private configuration off argv."""
	request = {"protocol": 1, "operation": "discover_mail", "directory": str(document.directory), "config_name": document.path.name,
		"config_sha256": hashlib.sha256(document.data).hexdigest(), "email": email}
	try:
		process = subprocess.run([sys.executable, "-B", str(Path(__file__).resolve())], input=json.dumps(request), capture_output=True,
			text=True, encoding="utf-8", cwd=ROOT, timeout=90)
		response = json.loads(process.stdout)
	except (OSError, ValueError, subprocess.TimeoutExpired) as error:
		raise ValueError("Mail discovery could not finish within 90 seconds. Check the connection or configure SMTP manually.") from error
	if not isinstance(response, dict):
		raise ValueError("Mail discovery returned an invalid response. Configure SMTP manually.")
	if process.returncode or response.get("protocol") != 1 or response.get("ok") is not True:
		raise ValueError("Mail discovery failed. Check saved settings and the connection, or configure SMTP manually.")
	result = response.get("result")
	if not isinstance(result, dict) or "match" not in result:
		raise ValueError("Mail discovery returned an invalid response. Configure SMTP manually.")
	match = result["match"]
	if match is not None:
		try:
			settings = match["settings"]
			if set(match) != {"provider", "security", "settings"} or set(settings) - {"smtp_server", "tls", "starttls", "email_username"}:
				raise ValueError
			host, port = settings["smtp_server"].rsplit(":", 1)
			expected = mail_settings((match["provider"], host, int(port), match["security"], settings.get("email_username")))
			if expected != match:
				raise ValueError
		except (KeyError, TypeError, AttributeError, ValueError) as error:
			raise ValueError("Mail discovery returned invalid settings. Configure SMTP manually.") from error
	return result


def main():
	try:
		data = sys.stdin.buffer.read(MAX_BYTES + 1)
		if len(data) > MAX_BYTES:
			raise ValueError("Mail discovery request is too large.")
		with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
			result = execute(json.loads(data))
		response = {"protocol": 1, "ok": True, "result": result}
	except (Exception, SystemExit):
		# Provider URLs, proxy credentials and raw configuration never reach IPC.
		response = {"protocol": 1, "ok": False, "error": "Mail discovery failed. Check saved settings and the connection, or configure SMTP manually."}
	print(json.dumps(response, ensure_ascii=True))
	return 0 if response["ok"] else 1


if __name__ == "__main__":
	sys.exit(main())
