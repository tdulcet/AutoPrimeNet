"""Tests for responsive job delivery and offline process calls.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import threading
import time
import unittest
from unittest import mock
from types import SimpleNamespace
import json

from gui_controller import BackgroundJobs, ControllerError, backend_request


class ControllerTests(unittest.TestCase):
	def test_repeated_click_is_rejected_until_result_consumed(self):
		jobs = BackgroundJobs()
		release = threading.Event()
		try:
			self.assertTrue(jobs.submit("first", release.wait, 2))
			self.assertFalse(jobs.submit("duplicate", lambda: None))
			release.set()
			deadline = time.monotonic() + 3
			result = None
			while result is None and time.monotonic() < deadline:
				result = jobs.take()
				if result is None:
					time.sleep(0.01)
			self.assertEqual(result, ("first", True, None))
			self.assertFalse(jobs.busy)
		finally:
			release.set()
			jobs.close()
		self.assertFalse(jobs.submit("closed", lambda: None))

	def test_backend_failure_is_not_reported_as_success(self):
		with self.assertRaisesRegex(ControllerError, "Unsupported offline bridge operation"):
			backend_request("unreserve_all")

	def test_oversized_request_rejected_before_launch(self):
		with self.assertRaisesRegex(ControllerError, "1 MiB"):
			backend_request("parse_work", lines=["x" * (1024 * 1024)])
	def test_malformed_backend_envelopes_are_controlled_errors(self):
		for response in (None, [], "unexpected", {},
			{"protocol": 1, "ok": True},
			{"protocol": 1, "ok": 1, "result": {}},
			{"protocol": 1, "ok": False, "error": {"private": "data"}}):
			with self.subTest(response=response), mock.patch(
				"gui_controller.subprocess.run",
				return_value=SimpleNamespace(stdout=json.dumps(response), returncode=0),
			):
				with self.assertRaisesRegex(ControllerError, "Unexpected offline backend response"):
					backend_request("capabilities")


if __name__ == "__main__":
	unittest.main()
