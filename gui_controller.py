"""Background jobs and owned helper processes for the optional GUI.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import queue
import subprocess
import sys
import threading
import time

from gui_tray_host import tray_platform


ROOT = Path(__file__).resolve().parent


class ControllerError(Exception):
	"""An operation failed without exposing raw subprocess diagnostics."""


def monitor_message(message):
	"""Validate fields used by Tk before accepting an event from the runner."""
	if not isinstance(message, dict) or not isinstance(message.get("event"), str):
		return False
	event = message["event"]
	if event not in {"ready", "cycle_started", "cycle_finished", "operation_finished", "failed", "stopped", "trace_created", "trace_warning"}:
		return False
	if event == "ready":
		if "operation" in message:
			from gui_operations import OPERATIONS
			if not isinstance(message["operation"], str) or message["operation"] not in OPERATIONS:
				return False
		elif type(message.get("interval")) is not int or not 0 <= message["interval"] <= 604800:
			return False
	for key in ("error", "assignment_backup"):
		if key in message and message[key] is not None and (not isinstance(message[key], str) or len(message[key]) > 8192):
			return False
	if "error" in message and message["error"] is None:
		return False
	if event == "trace_created":
		name = message.get("name")
		if not isinstance(name, str) or not name or len(name) > 255 or Path(name).name != name or any(char in name for char in "\r\n\x00"):
			return False
	if event == "cycle_finished":
		for key in ("time", "next_cycle"):
			value = message.get(key)
			if type(value) not in (int, float):
				return False
			try:
				time.localtime(value)
			except (ValueError, OverflowError, OSError):
				return False
	return True


class BackgroundJobs:
	"""One bounded job at a time; callers consume results on the Tk thread."""

	def __init__(self):
		self.events = queue.Queue()
		self._executor = ThreadPoolExecutor(max_workers=1, thread_name_prefix="GUI")
		self._future = None
		self._closed = False

	@property
	def busy(self):
		return self._future is not None

	def submit(self, name, function, *args):
		if self._closed or self.busy:
			return False
		self._future = self._executor.submit(function, *args)
		# Set the future before adding the callback: already-completed futures
		# may invoke it synchronously. Queue delivery does not touch Tk widgets.
		self._future.add_done_callback(lambda future: self.events.put((name, future)))
		return True

	def take(self):
		try:
			name, future = self.events.get_nowait()
		except queue.Empty:
			return None
		self._future = None
		try:
			return name, future.result(), None
		except Exception as error:
			return name, None, error

	def close(self):
		self._closed = True
		self._executor.shutdown(wait=False, cancel_futures=True)


def backend_request(operation, **parameters):
	"""Call the offline bridge; its timeout bounds background process lifetime."""
	request = {"protocol": 1, "operation": operation, **parameters}
	payload = json.dumps(request)
	if len(payload.encode("utf-8")) > 1024 * 1024:
		raise ControllerError("The offline preview request exceeds the 1 MiB limit.")
	try:
		process = subprocess.run(
			[sys.executable, "-B", str(ROOT / "gui_backend.py")],
			input=payload, capture_output=True, text=True,
			encoding="utf-8", cwd=ROOT, timeout=30,
		)
		response = json.loads(process.stdout)
	except (OSError, ValueError, subprocess.TimeoutExpired) as error:
		raise ControllerError("The offline backend could not complete. Check the selected Python environment.") from error
	if not isinstance(response, dict) or response.get("protocol") != 1:
		raise ControllerError("Unexpected offline backend response.")
	if response.get("ok") is not True or process.returncode:
		# Only the bridge's explicit failure envelope may supply an error.
		error = response.get("error")
		if response.get("ok") is not False or not isinstance(error, str) or not error:
			error = "Unexpected offline backend response."
		raise ControllerError(error)
	if "result" not in response:
		raise ControllerError("Unexpected offline backend response.")
	return response["result"]


class TrayController:
	"""Own a separate native tray event loop and receive its menu events."""

	def __init__(self, process_factory=None):
		self.events = queue.Queue()
		self.process = None
		self.ready = False
		self.state = "Stopped"
		self.generation = 0
		self._process_factory = process_factory or subprocess.Popen
		self._stopping_process = None

	def start(self):
		if self.process is not None and self.process.poll() is None:
			return
		self.generation += 1
		self.ready = False
		if not tray_platform():
			self.events.put({"event": "unavailable", "generation": self.generation})
			return
		try:
			self.process = self._process_factory(
				[sys.executable, "-B", str(ROOT / "gui_tray.py")],
				stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
				text=True, encoding="utf-8", cwd=ROOT,
			)
		except OSError:
			self.events.put({"event": "unavailable", "generation": self.generation})
			return
		threading.Thread(target=self._read, args=(self.process, self.generation), name="TrayEvents", daemon=True).start()

	def _read(self, process, generation):
		try:
			for line in process.stdout:
				try:
					event = json.loads(line).get("event")
				except (ValueError, AttributeError):
					continue
				if isinstance(event, str) and event in {"ready", "open", "quit", "start", "stop", "unavailable"}:
					self.events.put({"event": event, "generation": generation})
		except (OSError, ValueError):
			pass
		finally:
			self.events.put({"event": "unavailable", "generation": generation})

	def set_state(self, state):
		self.state = state
		if self.process is not None and self.process.poll() is None and self.process.stdin is not None:
			try:
				self.process.stdin.write(json.dumps({"state": state}) + "\n")
				self.process.stdin.flush()
			except (OSError, ValueError):
				pass

	def stop(self):
		self.ready = False
		if self.process is None or self._stopping_process is self.process:
			return
		self._stopping_process = self.process
		self.generation += 1  # Ignore late readiness/menu events from this attempt.
		if self.process is not None and self.process.stdin is not None:
			try:
				self.process.stdin.close()
			except OSError:
				pass
		# Reap only our helper in a background thread; never block Tk's event loop.
		if self.process is not None:
			threading.Thread(target=self._reap, args=(self.process,), name="TrayShutdown").start()

	def _reap(self, process):
		try:
			process.wait(timeout=3)
		except subprocess.TimeoutExpired:
			process.terminate()
			try:
				process.wait(timeout=2)
			except subprocess.TimeoutExpired:
				process.kill()
				process.wait()
		finally:
			process.stdout.close()


class MonitorController:
	"""Own scheduled/one-shot execution and expose sanitized events to Tk."""

	def __init__(self, process_factory=None):
		self.events = queue.Queue()
		self.process = None
		self.state = "Stopped"
		self._control_lock = threading.Lock()
		self.generation = 0
		self._process_factory = process_factory or subprocess.Popen

	@property
	def active(self):
		return self.process is not None and self.process.poll() is None

	def start(self, document, operation=None, parameters=None):
		if self.active:
			raise ControllerError("A GUI-owned AutoPrimeNet runner is already active.")
		if document.version is None:
			raise ControllerError("Save the configuration before starting AutoPrimeNet.")
		request = {
			"protocol": 1, "directory": str(document.directory), "config_name": document.path.name,
			"config_sha256": hashlib.sha256(document.data).hexdigest(),
		}
		if operation is not None:
			from gui_operations import operation_arguments
			try:
				operation_arguments(operation, parameters)
			except ValueError as error:
				raise ControllerError(str(error)) from error
			request["operation"] = operation
			if parameters:
				request["parameters"] = parameters
		elif parameters:
			raise ControllerError("Scheduled monitoring does not accept operation parameters.")
		process = None
		try:
			process = self._process_factory(
				[sys.executable, "-B", str(ROOT / "gui_monitor.py")],
				stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
				text=True, encoding="utf-8", cwd=ROOT,
			)
			process.stdin.write(json.dumps(request) + "\n")
			process.stdin.flush()
		except (OSError, ValueError) as error:
			if process is not None:
				# Retain ownership until cleanup finishes; never wait on Tk's thread.
				self.process = process
				self.state = "Stopping"
				self.generation += 1
				threading.Thread(target=self._abort_start, args=(process, self.generation), name="RunnerStartupCleanup").start()
			raise ControllerError("Could not launch the AutoPrimeNet runner.") from error
		self.process = process
		self.state = "Starting"
		self.generation += 1
		threading.Thread(target=self._read, args=(process, self.generation), name="MonitoringEvents", daemon=True).start()

	def _abort_start(self, process, generation):
		# No begin handshake was sent, so this child cannot have started a cycle.
		try:
			if process.poll() is None:
				try:
					process.terminate()
				except ProcessLookupError:
					pass  # The child exited between poll and terminate.
			try:
				code = process.wait(timeout=2)
			except subprocess.TimeoutExpired:
				try:
					process.kill()
				except ProcessLookupError:
					pass
				code = process.wait()
		finally:
			for stream in (process.stdin, process.stdout):
				try:
					stream.close()
				except (OSError, ValueError):
					pass
		self.events.put({"event": "exited", "exit_code": code, "generation": generation})

	def _read(self, process, generation):
		try:
			for line in process.stdout:
				try:
					message = json.loads(line)
				except ValueError:
					continue
				if monitor_message(message):
					if message["event"] == "ready":
						with self._control_lock:
							if generation == self.generation and self.state == "Starting":
								process.stdin.write(json.dumps({"command": "begin"}) + "\n")
								process.stdin.flush()
					self.events.put({**message, "generation": generation})
		except (OSError, ValueError):
			pass
		finally:
			code = process.wait()
			with self._control_lock:
				try:
					process.stdin.close()
				except (OSError, ValueError):
					pass
			process.stdout.close()
			self.events.put({"event": "exited", "exit_code": code, "generation": generation})

	def stop(self, force=False):
		with self._control_lock:
			if not self.active:
				return
			self.state = "Stopping"
			try:
				self.process.stdin.write(json.dumps({"command": "force-stop" if force else "stop"}) + "\n")
				self.process.stdin.flush()
			except (OSError, ValueError):
				pass
