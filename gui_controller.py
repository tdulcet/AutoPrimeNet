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


ROOT = Path(__file__).resolve().parent


class ControllerError(Exception):
	"""An operation failed without exposing raw subprocess diagnostics."""


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
	if response.get("protocol") != 1 or not response.get("ok") or process.returncode:
		raise ControllerError(response.get("error", "Unexpected offline backend response."))
	return response["result"]


class TrayController:
	"""Own a separate native tray event loop and receive its menu events."""

	def __init__(self):
		self.events = queue.Queue()
		self.process = None
		self.ready = False
		self.state = "Stopped"

	def start(self):
		if self.process is not None and self.process.poll() is None:
			return
		if sys.platform not in {"darwin", "win32"}:
			self.events.put("unavailable")
			return
		try:
			self.process = subprocess.Popen(
				[sys.executable, "-B", str(ROOT / "gui_tray.py")],
				stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
				text=True, encoding="utf-8", cwd=ROOT,
			)
		except OSError:
			self.events.put("unavailable")
			return
		threading.Thread(target=self._read, name="TrayEvents", daemon=True).start()

	def _read(self):
		try:
			for line in self.process.stdout:
				try:
					event = json.loads(line).get("event")
				except (ValueError, AttributeError):
					continue
				if event in {"ready", "open", "quit", "start", "stop", "unavailable"}:
					self.events.put(event)
		except (OSError, ValueError):
			pass
		finally:
			self.events.put("unavailable")

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
		if self.process is not None and self.process.stdin is not None:
			try:
				self.process.stdin.close()
			except OSError:
				pass
		# Reap only our helper in a background thread; never block Tk's event loop.
		if self.process is not None:
			threading.Thread(target=self._reap, name="TrayShutdown").start()

	def _reap(self):
		try:
			self.process.wait(timeout=3)
		except subprocess.TimeoutExpired:
			self.process.terminate()
			try:
				self.process.wait(timeout=2)
			except subprocess.TimeoutExpired:
				self.process.kill()
				self.process.wait()
		finally:
			self.process.stdout.close()


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

	def start(self, document, operation=None):
		if self.active:
			raise ControllerError("A GUI-owned AutoPrimeNet runner is already active.")
		if document.version is None:
			raise ControllerError("Save the configuration before starting AutoPrimeNet.")
		request = {
			"protocol": 1, "directory": str(document.directory), "config_name": document.path.name,
			"config_sha256": hashlib.sha256(document.data).hexdigest(),
		}
		if operation is not None:
			from gui_operations import OPERATIONS
			if operation not in OPERATIONS:
				raise ControllerError("Unsupported one-shot operation.")
			request["operation"] = operation
		try:
			process = self._process_factory(
				[sys.executable, "-B", str(ROOT / "gui_monitor.py")],
				stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
				text=True, encoding="utf-8", cwd=ROOT,
			)
			process.stdin.write(json.dumps(request) + "\n")
			process.stdin.flush()
		except OSError as error:
			if "process" in locals():
				process.stdin.close()
				process.wait(timeout=5)
				process.stdout.close()
			raise ControllerError("Could not launch the AutoPrimeNet runner.") from error
		self.process = process
		self.state = "Starting"
		self.generation += 1
		threading.Thread(target=self._read, args=(process, self.generation), name="MonitoringEvents", daemon=True).start()

	def _read(self, process, generation):
		try:
			for line in process.stdout:
				try:
					message = json.loads(line)
				except ValueError:
					continue
				if isinstance(message, dict) and message.get("event") in {"ready", "cycle_started", "cycle_finished", "operation_finished", "failed", "stopped"}:
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
