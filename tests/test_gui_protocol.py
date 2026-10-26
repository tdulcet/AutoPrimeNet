"""Private helper entry-point rejection and output-channel boundaries.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import json
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
HELPERS = ("gui_backend.py", "gui_monitor.py", "gui_runtime.py", "gui_registration.py", "gui_mail_discovery.py")


class ProtocolTests(unittest.TestCase):
	def test_invalid_requests_fail_without_echoing_private_input(self):
		for helper in HELPERS:
			for payload in ('{"private-fixture":', '"private-fixture"', 'null', '[]'):
				with self.subTest(helper=helper, payload=payload):
					process = subprocess.run([sys.executable, "-B", str(ROOT / helper)], input=payload + "\n",
						capture_output=True, text=True, cwd=ROOT, timeout=10)
					self.assertNotEqual(process.returncode, 0)
					self.assertNotIn("private-fixture", process.stdout + process.stderr)
					if helper == "gui_registration.py":
						self.assertEqual(process.stdout, "")
					else:
						response = json.loads(process.stdout)
						self.assertTrue(response.get("ok") is False or response.get("event") == "failed")

	def test_oversize_requests_are_bounded_at_each_helper_entry_point(self):
		for helper in HELPERS:
			with self.subTest(helper=helper):
				process = subprocess.run([sys.executable, "-B", str(ROOT / helper)], input="private-fixture" + "x" * (1024 * 1024 + 1),
					capture_output=True, text=True, cwd=ROOT, timeout=10)
				self.assertNotEqual(process.returncode, 0)
				self.assertNotIn("private-fixture", process.stdout + process.stderr)
				self.assertLess(len(process.stdout + process.stderr), 2048)

	def test_native_entry_point_separates_console_output_and_observes_parent_eof(self):
		code = '''
import gui_runtime, sys
def execute(request, stop, emit):
    assert stop.wait(2), 'control reader did not observe parent EOF'
    print('private-native-console-fixture')
    emit({'event': 'cycle_started', 'time': 0})
    return 0
gui_runtime.execute = execute
sys.exit(gui_runtime.main())
'''
		process = subprocess.run([sys.executable, "-B", "-c", code], input="{}\n", capture_output=True, text=True, cwd=ROOT, timeout=5)
		self.assertEqual(process.returncode, 0, process.stderr)
		self.assertEqual(json.loads(process.stdout), {"event": "cycle_started", "time": 0})
		self.assertEqual(process.stderr.strip(), "private-native-console-fixture")
