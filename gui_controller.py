"""Background jobs and owned helper processes for the optional GUI.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from concurrent.futures import ThreadPoolExecutor
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

	def start(self):
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
				if event in {"ready", "open", "quit", "unavailable"}:
					self.events.put(event)
		except (OSError, ValueError):
			pass
		finally:
			self.events.put("unavailable")

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
