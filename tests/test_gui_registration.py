"""Graphical registration tests with socket blocking and simulated APIs.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument
from gui_controller import ControllerError, MonitorController, backend_request
from gui_monitor import StopControl, _cli_once
from gui_registration_plan import FormAnswers, validate_shape
from test_gui_monitor import fake_monitor_process, fixture, wait_event


TEXT = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n"


def preview(directory, entries, worker=1, text=TEXT):
	return backend_request("preview_registration", directory=directory, text=text, parameters={"worker": worker, "entries": entries})


class RegistrationTests(unittest.TestCase):
	def test_original_constructor_and_formatter_for_all_eight_work_types(self):
		expected = {2: "Factor=127,70,72", 3: "Pminus1=1,2,127,-1,100000,10000000,70", 4: "Pfactor=1,2,127,-1,70,1.3", 5: "ECM2=1,2,127,-1,100000,10000000,100", 100: "Test=127,70,0", 101: "DoubleCheck=127,70,0", 150: "PRP=1,2,127,-1,70,1.3", 151: "PRPDC=1,2,127,-1,70,1.3,3,1"}
		with tempfile.TemporaryDirectory() as directory:
			for kind, line in expected.items():
				with self.subTest(kind=kind):
					result = preview(directory, [{"work_type": kind, "exponent": 127}])
					self.assertEqual(result["lines"], [line])
					self.assertFalse(result["files_written"])
					self.assertFalse(result["network_enabled"])
			self.assertEqual(list(Path(directory).iterdir()), [])

	def test_batch_factors_and_gpuowl_bounds_follow_original_workflow(self):
		with tempfile.TemporaryDirectory() as directory:
			result = preview(directory, [{"exponent": 11, "known_factors": [23, 89]}, {"work_type": 151, "exponent": 11, "prp_residue_type": 5, "known_factors": [23]}])
			self.assertTrue(result["lines"][0].endswith('"23,89"'))
			self.assertIn(",3,5,", result["lines"][1])
			gpu = preview(directory, [{"exponent": 127, "B1": 100, "B2": 1000}], text=TEXT.replace("mlucas", "gpuowl"))
			self.assertTrue(gpu["lines"][0].startswith("B1=100,B2=1000;PRP="))

	def test_composite_exponents_bad_factors_and_worker_are_rejected_offline(self):
		with tempfile.TemporaryDirectory() as directory:
			for row in ({"exponent": 12}, {"exponent": 11, "known_factors": [9]}, {"exponent": 11, "known_factors": [5]}, {"exponent": 11, "known_factors": [23, 23]}):
				with self.subTest(row=row), self.assertRaises(ControllerError):
					preview(directory, [row])
			with self.assertRaisesRegex(ControllerError, "worker is not configured"):
				preview(directory, [{"exponent": 127}], worker=2)
			self.assertEqual(list(Path(directory).iterdir()), [])

	def test_shape_limits_and_prompt_drift_fail_closed(self):
		for row in ({"exponent": 0}, {"exponent": True}, {"exponent": 127, "work_type": 200}, {"exponent": 127, "tests_saved": float("nan")}, {"exponent": 127, "B1": 99}, {"exponent": 127, "work_type": 2, "sieve_depth": 70.5}, {"exponent": 127, "work_type": 151, "known_factors": [23]}):
			with self.subTest(row=row), self.assertRaises(ValueError):
				validate_shape({"worker": 1, "entries": [row]})
		with self.assertRaises(ValueError):
			validate_shape({"worker": 1, "entries": [{"exponent": 127}] * 2})
		answers = FormAnswers(validate_shape({"worker": 1, "entries": [{"exponent": 127}]}))
		self.assertEqual(answers.integer("Exponent to test", None, 2, 10000000000), 127)
		with self.assertRaises(ValueError):
			answers.integer("Exponent to test", None)
		with self.assertRaises(ValueError):
			answers.boolean("Unexpected new prompt", False)

	def run_adapter(self, document, operation, parameters=None):
		request = dict(directory=str(document.directory), config_name=document.path.name, config_sha256=hashlib.sha256(document.data).hexdigest(), operation=operation, parameters=parameters or {})
		code = '''import sys,json
from pathlib import Path
import gui_backend as b, gui_registration as r
sys.addaudithook(b._network_guard)
request=json.loads(sys.stdin.read())
record=Path(request['directory'])/'api.record'
def before(ns):
    def send(args, adapter, guid, params):
        with record.open('a') as stream: stream.write(params['t']+'\\n')
        if params['t']=='uc':
            return dict(pnErrorResult='0',u=args.user_id,cn=args.computer_id,un='Fixture',od='0',g='a'*32)
        if params['t']=='po': return dict(pnErrorResult='0')
        raise AssertionError('Unexpected API transaction')
    def register(config,args,adapter,cpu,assignment):
        with record.open('a') as stream: stream.write(str(assignment.n)+'\\n')
        assignment.uid='b'*32
        return assignment
    ns['send_request']=send
    ns['register_assignment']=register
    def no(*args): raise AssertionError('Unexpected work request, setup prompt or email')
    ns['setup']=ns['get_assignment']=ns['test_msg']=no
sys.exit(r.execute(request,before_main=before))
'''
		return subprocess.run([sys.executable, "-B", "-c", code], input=json.dumps(request), capture_output=True, text=True, timeout=30)

	def test_computer_registration_reuses_original_uc_po_without_work_fetch(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			process = self.run_adapter(document, "register_computer")
			self.assertEqual(process.returncode, 0, process.stderr)
			self.assertEqual((Path(directory) / "api.record").read_text(), "uc\npo\n")
			self.assertEqual(ConfigDocument(directory).config.get("PrimeNet", "ComputerGUID"), "a" * 32)
			self.assertFalse((Path(directory) / "worktodo.txt").exists())

	def test_original_registration_appends_batch_and_registers_existing_unregistered_work(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			document.path.write_text(document.text + "ComputerGUID=" + "a" * 32 + "\n")
			document = ConfigDocument(directory)
			work = Path(directory) / "worktodo.txt"
			work.write_text("Test=107,70,1\n")
			process = self.run_adapter(document, "register_exponents", {"worker": 1, "entries": [{"work_type": 100, "exponent": 127}, {"work_type": 101, "exponent": 131}]})
			self.assertEqual(process.returncode, 0, process.stderr)
			self.assertEqual((Path(directory) / "api.record").read_text(), "107\n127\n131\n")
			self.assertEqual(work.read_text().count("b" * 32), 3)
			self.assertIn("DoubleCheck=", work.read_text())

	def test_adapter_rejects_stale_configuration_before_startup(self):
		from gui_registration import execute
		with tempfile.TemporaryDirectory() as directory:
			fixture(directory)
			with self.assertRaisesRegex(ValueError, "changed before registration"):
				execute(dict(operation="register_computer", directory=directory, config_name="prime.ini", config_sha256="wrong"))
			self.assertEqual({path.name for path in Path(directory).iterdir()}, {"prime.ini"})

	def test_registration_targets_selected_multiworker_or_prpll_work_file(self):
		for engine in ("mlucas", "prpll"):
			with self.subTest(engine=engine), tempfile.TemporaryDirectory() as directory:
				base = Path(directory)
				text = TEXT.replace("mlucas", engine) + "NumWorkers=2\nComputerGUID=" + "a" * 32 + "\n"
				if engine == "mlucas":
					for name in ("one", "two"):
						(base / name).mkdir()
					text += "[Worker #1]\ndirectory=one\n[Worker #2]\ndirectory=two\n"
					first, target = base / "one/worktodo.txt", base / "two/worktodo.txt"
				else:
					first, target = base / "worktodo-0.txt", base / "worktodo-1.txt"
				(base / "prime.ini").write_text(text)
				first.write_text("Test=107,70,1\n")
				process = self.run_adapter(ConfigDocument(directory), "register_exponents", {"worker": 2, "entries": [{"exponent": 127}]})
				self.assertEqual(process.returncode, 0, process.stderr)
				self.assertEqual(first.read_text(), "Test=107,70,1\n")
				self.assertIn("b" * 32, target.read_text())
				self.assertEqual((base / "api.record").read_text(), "127\n")

	def test_structured_child_payload_keeps_plan_out_of_command_line(self):
		with tempfile.TemporaryDirectory() as directory, patch("gui_monitor.subprocess.Popen") as popen:
			document = fixture(directory)
			popen.return_value.wait.return_value = 0
			parameters = {"worker": 1, "entries": [{"exponent": 127}]}
			self.assertEqual(_cli_once(directory, "prime.ini", StopControl(), operation="register_exponents", parameters=parameters), (0, False))
			self.assertTrue(popen.call_args.args[0][-1].endswith("gui_registration.py"))
			request = json.loads(popen.return_value.stdin.write.call_args.args[0])
			self.assertEqual(request["parameters"], parameters)
			self.assertEqual(request["config_sha256"], hashlib.sha256(document.data).hexdigest())
			self.assertNotIn("127", " ".join(popen.call_args.args[0]))

	def test_supervisor_previews_and_snapshots_registration_before_simulated_launch(self):
		with tempfile.TemporaryDirectory() as directory:
			document = fixture(directory)
			document.path.write_text(document.text + "ComputerGUID=" + "a" * 32 + "\n")
			document = ConfigDocument(directory)
			controller = MonitorController(process_factory=fake_monitor_process)
			controller.start(document, operation="register_exponents", parameters={"worker": 1, "entries": [{"exponent": 127}]})
			ready = wait_event(controller, "ready")
			self.assertTrue(Path(ready["assignment_backup"], "manifest.json").exists())
			wait_event(controller, "exited")
			self.assertEqual((Path(directory) / "operation.record").read_text(), "register_exponents")
			self.assertFalse((Path(directory) / "worktodo.txt").exists())


if __name__ == "__main__":
	unittest.main()
