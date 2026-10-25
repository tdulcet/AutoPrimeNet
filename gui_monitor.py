#!/usr/bin/env python3
"""Owned CLI helper for scheduled monitoring and one-shot actions.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time

from gui_backend import BackendError, _read_source
from gui_config import ConfigDocument, WorkspaceError, instance_lease, inspect_workspace
from gui_controller import ControllerError, ROOT, backend_request
from gui_operations import OPERATIONS, operation_arguments
from gui_assignment_backup import snapshot_assignments


class StopControl:
	def __init__(self):
		self.stop = threading.Event()
		self.force = threading.Event()
		self.begin = threading.Event()

	def read(self, stream):
		for line in stream:
			try:
				command = json.loads(line).get("command")
			except (ValueError, AttributeError):
				continue
			if command == "stop":
				self.stop.set()
			elif command == "begin":
				self.begin.set()
			elif command == "force-stop":
				self.force.set()
				self.stop.set()
		# A parent crash also requests shutdown, without interrupting a write.
		self.stop.set()


def _cli_once(directory, config_name, control, operation=None, parameters=None, expected_hash=None):
	"""Run only our CLI child; forced termination requires a separate command."""
	if operation is None and parameters:
		raise ValueError("Scheduled cycles do not accept operation parameters.")
	_read_source(ROOT / "autoprimenet.py")
	environment = dict(os.environ)
	environment["NO_COLOR"] = "1"
	environment.pop("FORCE_COLOR", None)
	flags = () if operation is None else operation_arguments(operation, parameters)
	registration = operation in {"register_computer", "register_exponents"}
	command = [sys.executable, "-B", str(ROOT / "gui_registration.py")] if registration else [sys.executable, "-B", str(ROOT / "autoprimenet.py"), "--workdir", str(directory), "--config-file", config_name, "--timeout", "0", *flags]
	payload = None
	if registration:
		request = {"operation": operation, "directory": str(directory), "config_name": config_name, "parameters": parameters or {}, "config_sha256": expected_hash or hashlib.sha256(ConfigDocument(directory, config_name).data).hexdigest()}
		payload = json.dumps(request).encode("utf-8")
		if len(payload) > 65536:
			raise WorkspaceError("Registration request exceeds the 64 KiB execution limit.")
	process = subprocess.Popen(
		command,
		stdin=subprocess.PIPE if registration else subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
		cwd=ROOT, env=environment,
	)
	if registration:
		try:
			process.stdin.write(payload)
		except OSError:
			pass  # Reap the child and report its exit status below.
		finally:
			try:
				process.stdin.close()
			except OSError:
				pass
	while True:
		try:
			return process.wait(timeout=0.2), False
		except subprocess.TimeoutExpired:
			if control.force.is_set():
				process.terminate()
				try:
					process.wait(timeout=3)
				except subprocess.TimeoutExpired:
					process.kill()
					process.wait()
				return process.returncode, True


def cli_cycle(directory, config_name, control):
	# The existing zero-timeout CLI registers a new computer and exits before
	# requesting work. Follow a completed initial registration with its normal
	# work cycle, unless Stop was requested in between. No API logic is copied.
	missing_guid = not ConfigDocument(directory, config_name).config.has_option("PrimeNet", "ComputerGUID")
	result = _cli_once(directory, config_name, control)
	if result == (0, False) and missing_guid and not control.stop.is_set():
		if ConfigDocument(directory, config_name).config.has_option("PrimeNet", "ComputerGUID"):
			return _cli_once(directory, config_name, control)
	return result


def run_schedule(directory, config_name, interval, control, emit, cycle=None, once=False):
	"""Serialize whole cycles. Exit zero alone does not confirm server success."""
	emit({"event": "ready", "interval": interval})
	cycle = cycle or cli_cycle
	# The parent acknowledges readiness only if Start is still wanted. A Stop
	# during offline preflight must not initiate the first server cycle afterward.
	while not control.begin.is_set() and not control.stop.wait(0.05):
		pass
	while not control.stop.is_set():
		started = time.time()
		monotonic_start = time.monotonic()
		emit({"event": "cycle_started", "time": started})
		code, forced = cycle(directory, config_name, control)
		if forced:
			emit({"event": "stopped", "forced": True})
			return 0
		if code:
			emit({"event": "failed", "exit_code": code})
			return 1
		# This is a local process-completion timestamp, never a claimed check-in.
		delay = max(interval - (time.monotonic() - monotonic_start), 0)
		emit({"event": "cycle_finished", "time": time.time(), "next_cycle": time.time() + delay, "server_confirmation": "unverified"})
		if once:
			break
		if control.stop.wait(delay):
			break
	emit({"event": "stopped", "forced": False})
	return 0


def native_cycle(directory, config_name, control, interval, expected_hash):
	"""Own one continuous native child; forward graceful stop, reap on force."""
	environment = dict(os.environ)
	environment["NO_COLOR"] = "1"
	environment.pop("FORCE_COLOR", None)
	process = subprocess.Popen([sys.executable, "-B", str(ROOT / "gui_runtime.py")], stdin=subprocess.PIPE,
		stderr=subprocess.DEVNULL, cwd=ROOT, env=environment)
	try:
		request = {"protocol": 1, "directory": str(directory), "config_name": config_name, "interval": interval, "config_sha256": expected_hash}
		process.stdin.write((json.dumps(request) + "\n").encode("utf-8"))
		process.stdin.flush()
		stop_sent = False
		while True:
			try:
				return process.wait(timeout=0.2), False
			except subprocess.TimeoutExpired:
				if control.force.is_set():
					process.terminate()
					try:
						process.wait(timeout=3)
					except subprocess.TimeoutExpired:
						process.kill()
						process.wait()
					return process.returncode, True
				if control.stop.is_set() and not stop_sent:
					try:
						process.stdin.write(b'{"command":"stop"}\n')
						process.stdin.flush()
					except OSError:
						pass
					stop_sent = True
	finally:
		try:
			process.stdin.close()
		except OSError:
			pass
		# EOF requests a boundary stop even if initial IPC failed.
		process.wait()


def run_native(directory, config_name, interval, watch, expected_hash, control, emit):
	emit({"event": "ready", "interval": interval, "watch": watch, "native_scheduler": True})
	while not control.begin.is_set() and not control.stop.wait(0.05):
		pass
	if control.stop.is_set():
		emit({"event": "stopped", "forced": False})
		return 0
	code, forced = native_cycle(directory, config_name, control, interval, expected_hash)
	if code and not forced:
		emit({"event": "failed", "exit_code": code})
		return 1
	emit({"event": "stopped", "forced": forced})
	return 0


def emit(message):
	print(json.dumps(message), flush=True)


def run_operation(directory, config_name, operation, control, emit, cycle=None, parameters=None, expected_hash=None):
	"""A confirmed action executes exactly once, without registration follow-up."""
	if operation not in OPERATIONS:
		raise WorkspaceError("Unsupported one-shot operation.")
	operation_arguments(operation, parameters)
	emit({"event": "ready", "operation": operation})
	while not control.begin.is_set() and not control.stop.wait(0.05):
		pass
	if control.stop.is_set():
		emit({"event": "stopped", "forced": False})
		return 0
	emit({"event": "cycle_started", "time": time.time(), "operation": operation})
	options = {"operation": operation}
	if parameters:
		options["parameters"] = parameters
	if expected_hash is not None and operation in {"register_computer", "register_exponents"}:
		options["expected_hash"] = expected_hash
	code, forced = (cycle or _cli_once)(directory, config_name, control, **options)
	if forced:
		emit({"event": "stopped", "forced": True})
		return 0
	if code:
		emit({"event": "failed", "exit_code": code})
		return 1
	emit({"event": "operation_finished", "operation": operation, "server_confirmation": "unverified"})
	emit({"event": "stopped", "forced": False})
	return 0


def main():
	try:
		# Avoid a buffered stdin lock held by the daemon control reader during
		# interpreter shutdown. No read-ahead can swallow an early Stop command.
		control_stream = os.fdopen(sys.stdin.fileno(), "rb", buffering=0, closefd=False)
		line = control_stream.readline(65537)
		if len(line) > 65536:
			raise WorkspaceError("Monitoring request is too large.")
		request = json.loads(line)
		if not isinstance(request, dict) or request.get("protocol") != 1:
			raise WorkspaceError("Unsupported monitoring protocol.")
		operation = request.get("operation")
		if operation is not None and operation not in OPERATIONS:
			raise WorkspaceError("Unsupported one-shot operation.")
		parameters = request.get("parameters")
		if operation is not None:
			operation_arguments(operation, parameters)
		elif parameters:
			raise WorkspaceError("Scheduled monitoring does not accept operation parameters.")
		document = ConfigDocument(request["directory"], request["config_name"])
		if document.bom:
			raise WorkspaceError("The original CLI cannot read UTF-8 BOM configurations. Keep a backup and save the INI as UTF-8 without BOM in your text editor, then refresh.")
		if document.version is None or hashlib.sha256(document.data).hexdigest() != request["config_sha256"]:
			raise WorkspaceError("Configuration changed. Reload before starting monitoring.")
		with instance_lease(document.directory, "~gui-monitor.lock"):
			# Check the CLI lock once before launch. Its own startup locks each
			# subsequent cycle, protecting against an independent CLI instance.
			with instance_lease(document.directory):
				settings = backend_request("validate_config", directory=str(document.directory), config_name=document.path.name, text=document.text)
				if operation in {"recover", "recover_all", "register_exponents"} and not document.config.get("PrimeNet", "ComputerGUID", fallback=""):
					raise WorkspaceError("This operation requires an existing computer registration. No assignments were requested.")
				if operation == "register_exponents":
					parameters = backend_request("preview_registration", directory=str(document.directory), config_name=document.path.name, text=document.text, parameters=parameters)["plan"]
				if operation == "unreserve":
					assignments = inspect_workspace(str(document.directory), document.path.name)["assignments"]
					if not any(item.get("fields", {}).get("n") == parameters["exponent"] for item in assignments):
						raise WorkspaceError("The exponent is not in the current local work files. Refresh before retrying.")
				if operation == "test_email":
					if not document.config.get("Email", "from_email", fallback="") or not document.config.get("Email", "smtp_server", fallback=""):
						raise WorkspaceError("Configure and save an SMTP server and From address before sending a test email.")
					if not document.config.getboolean("Email", "send", fallback=True):
						raise WorkspaceError("Notifications are disabled. Enable and save notification sending before testing.")
				if ConfigDocument(str(document.directory), document.path.name).version != document.version:
					raise WorkspaceError("Configuration changed during startup. Reload before retrying.")
				assignment_backup = None
				if operation is not None and OPERATIONS[operation].backup_work:
					assignment_backup = snapshot_assignments(str(document.directory), document.path.name, operation, parameters)
					if ConfigDocument(str(document.directory), document.path.name).version != document.version:
						raise WorkspaceError("Configuration changed during assignment backup. Reload before retrying.")
				# The unmodified CLI may normalize comments/formatting when writing
				# state. Preserve one private original snapshot before each Start.
				with tempfile.NamedTemporaryFile(prefix=document.path.name + ".gui-monitor-backup-", suffix=".bak", dir=document.directory, delete=False) as backup:
					backup.write(document.data)
					backup.flush()
					os.fsync(backup.fileno())
			control = StopControl()
			threading.Thread(target=control.read, args=(control_stream,), name="MonitorControl", daemon=True).start()
			def report(message):
				if message["event"] == "ready":
					message = {**message, "backup_created": True, "assignment_backup": assignment_backup}
				emit(message)
			if operation is not None:
				return run_operation(document.directory, document.path.name, operation, control, report, parameters=parameters, expected_hash=hashlib.sha256(document.data).hexdigest())
			if settings["timeout"] == 0:
				return run_schedule(document.directory, document.path.name, 0, control, report, once=True)
			return run_native(document.directory, document.path.name, settings["timeout"], settings["watch"], hashlib.sha256(document.data).hexdigest(), control, report)
	except (BackendError, WorkspaceError, ControllerError) as error:
		emit({"event": "failed", "error": str(error)})
		return 1
	except Exception:
		# Neither config text, credentials nor raw CLI output cross this channel.
		emit({"event": "failed", "error": "The AutoPrimeNet runner could not start or continue. Check configuration, instance locks and the AutoPrimeNet log."})
		return 1


if __name__ == "__main__":
	sys.exit(main())
