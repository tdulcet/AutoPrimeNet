"""Configuration persistence tests using disposable workspaces only.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from configparser import ConfigParser
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import json
import textwrap
from unittest.mock import patch

from gui_config import ConfigDocument, WorkspaceError, instance_lease, load_editor_workspace, patch_ini, save_configuration
from gui_controller import ControllerError, backend_request
from gui_options import validate_fields


def form(document, **changes):
	values = document.values()
	values["username"] = "ANONYMOUS"
	values.update(changes)
	return values


class SaveTests(unittest.TestCase):
	def test_hardware_fields_round_trip_without_changing_estimates(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nCustom=keep\n[Internals]\nRollingAverage=1234\nmsec_per_iter=42\nexponent=127\n")
			document = ConfigDocument(directory)
			changes = dict(CpuBrand="Fixture CPU/GPU", cpu_features="avx2 fma", CpuSpeed="3200", memory="8192", Memory="4096", WorkerDiskSpace="2.5", L1="64", L2="1024", L3="0", NumCores="8", CpuNumHyperthreads="0")
			result = save_configuration(document, form(document, **changes), "mlucas", [{"directory": "", "preference": ""}])
			for key, value in changes.items():
				self.assertEqual(result["document"].values()[key], value)
			config = result["document"].config
			self.assertEqual(config.getint("PrimeNet", "memory"), 8192)
			self.assertEqual(config.getint("PrimeNet", "Memory"), 4096)
			self.assertEqual(config.get("PrimeNet", "Custom"), "keep")
			self.assertEqual(config.getint("Internals", "RollingAverage"), 1234)
			self.assertEqual(config.getint("Internals", "msec_per_iter"), 42)
			unchanged = save_configuration(result["document"], result["document"].values(), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIsNone(unchanged["backup"])
			reset = save_configuration(result["document"], form(result["document"], **{key: "" for key in changes}), "mlucas", [{"directory": "", "preference": ""}])
			for key in changes:
				self.assertFalse(reset["document"].config.has_option("PrimeNet", key))

	def test_invalid_hardware_fields_never_replace_configuration(self):
		for changes in (dict(memory="1024", Memory="2048"), dict(CpuSpeed="3.2"), dict(WorkerDiskSpace="nan"), dict(NumCores="eight"), dict(CpuBrand="injected\nMemory=0")):
			with self.subTest(changes=changes), tempfile.TemporaryDirectory() as directory:
				path = Path(directory) / "prime.ini"
				path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
				document = ConfigDocument(directory)
				with self.assertRaises((WorkspaceError, ControllerError)):
					save_configuration(document, form(document, **changes), "mlucas", [{"directory": "", "preference": ""}])
				self.assertEqual(path.read_bytes(), document.data)
				self.assertFalse(list(Path(directory).glob("*.bak")))

	def test_notification_fields_use_email_section_and_round_trip(self):
		with tempfile.TemporaryDirectory() as directory:
			document = ConfigDocument(directory)
			changes = dict(notification_send="True", from_email="sender@example.org", to_emails="one@example.org, two@example.org", smtp_server="localhost:2525", email_username="smtp-account", tls="False", starttls="True")
			result = save_configuration(document, form(document, **changes), "mlucas", [{"directory": "", "preference": ""}])
			config = result["document"].config
			self.assertEqual(config.get("PrimeNet", "username"), "ANONYMOUS")
			self.assertEqual(config.get("Email", "username"), "smtp-account")
			self.assertEqual(config.get("Email", "to_emails"), "one@example.org,two@example.org")
			self.assertTrue(config.getboolean("Email", "send"))
			self.assertTrue(config.getboolean("Email", "starttls"))
			loaded = load_editor_workspace(directory)["document"]
			self.assertEqual(loaded.values()["email_username"], "smtp-account")
			unchanged = save_configuration(loaded, loaded.values(), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIsNone(unchanged["backup"])

	def test_notification_validation_refuses_invalid_data_without_writing(self):
		base = dict(from_email="sender@example.org", smtp_server="localhost")
		for changes in (dict(from_email="invalid"), dict(smtp_server="http://localhost"), dict(tls="True", starttls="True"), dict(to_emails="one@example.org,,two@example.org"), dict(to_emails="invalid"), dict(email_username="injected\npassword=bad"), dict(smtp_server="")):
			with self.subTest(changes=changes), tempfile.TemporaryDirectory() as directory:
				document = ConfigDocument(directory)
				with self.assertRaises((ControllerError, WorkspaceError)):
					save_configuration(document, form(document, **(base | changes)), "mlucas", [{"directory": "", "preference": ""}])
				self.assertFalse(document.path.exists())
				self.assertFalse(list(Path(directory).glob("*.bak")))

	def test_notification_disable_and_inherit_preserve_unrelated_credentials(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = "# retained\n[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n[Email]\nfrom_email=sender@example.org\nsmtp_server=localhost\nusername=account\npassword=fixture-secret\nsend=yes\nCustom=keep\n"
			path.write_text(original)
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document, notification_send="False"), "mlucas", [{"directory": "", "preference": ""}])
			self.assertFalse(result["document"].config.getboolean("Email", "send"))
			self.assertIn("password=fixture-secret\n", result["document"].text)
			self.assertIn("Custom=keep\n", result["document"].text)
			self.assertEqual(Path(result["backup"]).read_text(), original)
			inherited = save_configuration(result["document"], form(result["document"], notification_send=""), "mlucas", [{"directory": "", "preference": ""}])
			self.assertFalse(inherited["document"].config.has_option("Email", "send"))
			self.assertIn("password=fixture-secret\n", inherited["document"].text)

	def test_advanced_options_round_trip_through_real_backend(self):
		with tempfile.TemporaryDirectory() as directory:
			document = ConfigDocument(directory)
			changes = dict(min_bit="70", max_bit="75", force_target_bits="True", tests_saved="1.5", pm1_multiplier="0.8", pm1_bounds="MID", ECMBoundsMultiplier="1.25", MaxECMCurves="12", convert_ll_to_prp="False", convert_prp_to_ll="True")
			result = save_configuration(document, form(document, **changes), "mlucas", [{"directory": "", "preference": ""}])
			for key, value in changes.items():
				self.assertEqual(result["document"].values()[key], value)
			loaded = load_editor_workspace(directory)
			self.assertIsNotNone(loaded)
			unchanged = save_configuration(result["document"], result["document"].values(), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIsNone(unchanged["backup"])

	def test_invalid_advanced_combination_preserves_original(self):
		for changes in (dict(min_bit="75", max_bit="70"), dict(convert_ll_to_prp="True", convert_prp_to_ll="True"), dict(pm1_bounds="INVALID"), dict(ECMBoundsMultiplier="nan")):
			with self.subTest(changes=changes), tempfile.TemporaryDirectory() as directory:
				path = Path(directory) / "prime.ini"
				path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n")
				document = ConfigDocument(directory)
				with self.assertRaises((ControllerError, WorkspaceError)):
					save_configuration(document, form(document, **changes), "mlucas", [{"directory": "", "preference": ""}])
				self.assertEqual(path.read_bytes(), document.data)
				self.assertFalse(list(Path(directory).glob("*.bak")))

	def test_new_configuration_is_validated_and_private(self):
		with tempfile.TemporaryDirectory() as directory:
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIsNone(result["backup"])
			self.assertEqual(result["document"].config.get("PrimeNet", "username"), "ANONYMOUS")
			if os.name != "nt":
				self.assertEqual(result["document"].path.stat().st_mode & 0o777, 0o600)
			self.assertEqual({path.name for path in Path(directory).iterdir()}, {"prime.ini", "~lock", "~gui-monitor.lock"})

	def test_backup_bom_crlf_unknown_keys_and_ciphertext_preserved(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "custom.ini"
			# Unrelated encrypted email data is not decrypted or rewritten by the
			# save layer. Mock only validation for this synthetic ciphertext.
			original = b'\xef\xbb\xbf; comment\r\n[PrimeNet]\r\nusername : old\r\nmlucas=True\r\nUnknown = keep\r\n[Email]\r\nencrypted_password=unchanged-ciphertext\r\n[Other]\r\nPayload=first\r\n\tusername=continuation, not a real key\r\n'
			path.write_bytes(original)
			if os.name != "nt":
				path.chmod(0o640)
			document = ConfigDocument(directory, "custom.ini")
			with patch("gui_config.backend_request", return_value={}):
				result = save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(Path(result["backup"]).read_bytes(), original)
			updated = path.read_bytes()
			self.assertTrue(updated.startswith(b"\xef\xbb\xbf"))
			self.assertNotIn(b"\n", updated.replace(b"\r\n", b""))
			self.assertIn(b"; comment\r\n", updated)
			self.assertIn(b"username : ANONYMOUS\r\n", updated)
			self.assertIn(b"Unknown = keep\r\n", updated)
			self.assertIn(b"encrypted_password=unchanged-ciphertext\r\n", updated)
			self.assertIn(b"\tusername=continuation, not a real key\r\n", updated)
			if os.name != "nt":
				self.assertEqual(path.stat().st_mode & 0o777, 0o640)
				self.assertEqual(Path(result["backup"]).stat().st_mode & 0o777, 0o600)

	def test_external_change_refused_even_with_restored_mtime_and_same_size(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=aaaa\nmlucas=True\n")
			document = ConfigDocument(directory)
			info = path.stat()
			path.write_text("[PrimeNet]\nusername=bbbb\nmlucas=True\n")
			os.utime(path, ns=(info.st_atime_ns, info.st_mtime_ns))
			with self.assertRaisesRegex(WorkspaceError, "changed outside"):
				save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIn("bbbb", path.read_text())
			self.assertEqual(list(Path(directory).glob("*.bak")), [])

	def test_noop_save_keeps_exact_bytes_and_does_not_create_backup(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = b"# Keep style\n[PrimeNet]\nusername : ANONYMOUS\nmlucas=yes\nCertWork=off\n"
			path.write_bytes(original)
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document, CertWork="False"), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIsNone(result["backup"])
			self.assertEqual(path.read_bytes(), original)

	def test_unchanged_interpolation_and_implicit_defaults_are_not_materialized(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=old\nmlucas=True\nNameBase=box\nComputerID=%(NameBase)s\n")
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIn("ComputerID=%(NameBase)s\n", result["document"].text)
			self.assertFalse(result["document"].config.has_option("PrimeNet", "HoursBetweenCheckins"))

	def test_literal_percent_paths_and_multiple_worker_preferences(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "worker%one").mkdir()
			(base / "two").mkdir()
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document, logfile="activity%progress.log"), "mlucas", [
				{"directory": "worker%one", "preference": "150"}, {"directory": "two", "preference": "101"},
			])
			config = result["document"].config
			self.assertEqual(config.get("Worker #1", "directory"), "worker%one")
			self.assertEqual(config.get("PrimeNet", "logfile"), "activity%progress.log")
			self.assertEqual(config.getint("Worker #2", "WorkPreference"), 101)
			self.assertIn("worker%%one", result["document"].text)

	def test_live_instance_lock_refuses_save_and_does_not_truncate_lock_file(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "~lock"
			path.write_text("retained lock data")
			document = ConfigDocument(directory)
			with instance_lease(directory):
				with self.assertRaisesRegex(WorkspaceError, "instance lock"):
					save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(path.read_text(), "retained lock data")
			self.assertFalse((Path(directory) / "prime.ini").exists())

	def test_invalid_configuration_never_replaces_file(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = b"[PrimeNet]\nusername=old\nmlucas=True\n"
			path.write_bytes(original)
			document = ConfigDocument(directory)
			with self.assertRaises(ControllerError):
				save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": "12"}])
			self.assertEqual(path.read_bytes(), original)
			self.assertFalse(list(Path(directory).glob("*.bak")))

	def test_failed_replace_retains_original_backup_and_cleans_temporary(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = b"[PrimeNet]\nusername=old\nmlucas=True\n"
			path.write_bytes(original)
			document = ConfigDocument(directory)
			with patch("gui_config.os.replace", side_effect=PermissionError("simulated read-only destination")):
				with self.assertRaises(PermissionError):
					save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(path.read_bytes(), original)
			self.assertEqual(list(Path(directory).glob(".gui-config-*")), [])
			backups = list(Path(directory).glob("prime.ini.gui-backup-*.bak"))
			self.assertEqual(len(backups), 1)
			self.assertEqual(backups[0].read_bytes(), original)

	def test_read_only_configuration_is_not_replaced_via_writable_directory(self):
		if os.name == "nt":
			self.skipTest("POSIX permission-mode test")
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=old\nmlucas=True\n")
			path.chmod(0o400)
			document = ConfigDocument(directory)
			with self.assertRaisesRegex(WorkspaceError, "read-only"):
				save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(path.read_bytes(), document.data)
			self.assertFalse(list(Path(directory).glob("*.bak")))

	def test_changed_during_validation_is_refused(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=old\nmlucas=True\n")
			document = ConfigDocument(directory)
			def external_editor(*_args, **_kwargs):
				path.write_text("[PrimeNet]\nusername=external\nmlucas=True\n")
			with patch("gui_config.backend_request", side_effect=external_editor):
				with self.assertRaisesRegex(WorkspaceError, "changed during"):
					save_configuration(document, form(document), "mlucas", [{"directory": "", "preference": ""}])
			self.assertIn("external", path.read_text())

	def test_engine_change_resets_estimates_but_preserves_inactive_worker_sections(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=old\nmlucas=True\n[Internals]\nmsec_per_iter=42\nexponent=127\n[Worker #7]\nCustom=keep\nmsec_per_iter=43\nexponent=131\n")
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document), "prpll", [{"directory": "", "preference": ""}])
			config = result["document"].config
			self.assertFalse(config.has_option("PrimeNet", "mlucas"))
			self.assertTrue(config.getboolean("PrimeNet", "prpll"))
			self.assertEqual(config.get("Worker #7", "Custom"), "keep")
			self.assertFalse(config.has_option("Worker #7", "exponent"))
			self.assertEqual(config.getint("Internals", "RollingAverage"), 1000)

	def test_hours_change_resets_only_rolling_average_like_upstream_setup(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nCPUHours=24\n[Internals]\nRollingAverage=1200\nmsec_per_iter=42\nexponent=127\n")
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document, CPUHours="12"), "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(result["document"].config.getint("Internals", "RollingAverage"), 1000)
			self.assertEqual(result["document"].config.getint("Internals", "msec_per_iter"), 42)

	def test_symlink_config_and_data_filename_conflicts_refused(self):
		with tempfile.TemporaryDirectory() as directory:
			base = Path(directory)
			(base / "worktodo.txt").write_text("[PrimeNet]\nusername=old\nmlucas=True\n")
			document = ConfigDocument(directory, "worktodo.txt")
			with self.assertRaisesRegex(WorkspaceError, "conflicts"):
				document.render(form(document), "mlucas", [{"directory": "", "preference": ""}])
			for name in ("worktodo.txt.lck", "sample.proof", "worktodo.add", "~gui-monitor.lock"):
				with self.subTest(name=name), self.assertRaises(WorkspaceError):
					ConfigDocument(directory, name)
			try:
				(base / "prime.ini").symlink_to(base / "worktodo.txt")
			except OSError:
				self.skipTest("Symlinks unavailable")
			with self.assertRaisesRegex(WorkspaceError, "symbolic"):
				ConfigDocument(directory)

	def test_patch_preserves_indentation_unknown_multiline_and_no_trailing_newline(self):
		text = "[PrimeNet]\nusername=old\n[Custom]\nvalue = first\n  username=not-a-key"
		updated = patch_ini(text, {("PrimeNet", "username"): "new", ("PrimeNet", "ComputerID"): "box"})
		self.assertIn("username=new\nComputerID=box\n[Custom]", updated)
		self.assertTrue(updated.endswith("  username=not-a-key"))
		with self.assertRaisesRegex(WorkspaceError, "multiline"):
			patch_ini(text, {("Custom", "value"): "replacement"})

	def test_numeric_nonfinite_and_injection_values_refused(self):
		for changes in ({"username": "bad\nmlucas=True"}, {"DaysOfWork": "nan"}, {"DaysOfWork": "inf"}, {"CertDailyCPULimit": "101"}, {"work_file": "../worktodo.txt"}):
			with self.subTest(changes=changes), self.assertRaises(ValueError):
				validate_fields({"username": "ANONYMOUS", **changes})

	def test_bad_form_values_fail_in_background_load_instead_of_tk_callback(self):
		for setting in ("CertWork=maybe", "logfile=%(missing)s", "[Email]\nsend=maybe", "[Email]\ntls=maybe"):
			with self.subTest(setting=setting), tempfile.TemporaryDirectory() as directory:
				(Path(directory) / "prime.ini").write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n" + setting + "\n")
				with self.assertRaisesRegex(WorkspaceError, "invalid form value"):
					load_editor_workspace(directory)


class InitializationTests(unittest.TestCase):
	def test_real_upstream_encryption_decryption_and_ciphertext_preservation(self):
		with tempfile.TemporaryDirectory() as directory:
			code = textwrap.dedent('''
				import gui_backend as b, sys, json
				from pathlib import Path
				from io import StringIO
				sys.addaudithook(b._network_guard)
				path = Path('autoprimenet.py').resolve()
				_, tree, boundary = b._read_source(path)
				ns = b._load_definitions(path, tree, boundary)
				if not ns['libcrypto']:
					print('null')
					sys.exit(0)
				text = '[PrimeNet]\\nusername=ANONYMOUS\\nmlucas=True\\nProxyHost=localhost:8080\\nProxyPass=fixture-secret\\n[Email]\\nfrom_email=sender@example.org\\nsmtp_server=localhost\\npassword=fixture-mail-secret\\n'
				b._validate_config(ns, tree, boundary, {'text': text, 'directory': sys.argv[1]})
				ns['args'].encrypt = True
				ns['encrypt'](ns['config'], ns['args'])
				buffer = StringIO()
				ns['config'].write(buffer)
				print(json.dumps(buffer.getvalue()))
				ns['session'].close()
			''')
			process = subprocess.run([sys.executable, "-B", "-c", code, directory], capture_output=True, text=True, timeout=30)
			self.assertEqual(process.returncode, 0, process.stderr)
			text = json.loads(process.stdout)
			if text is None:
				self.skipTest("Native OpenSSL encryption unavailable")
			self.assertIn("encrypted_ProxyPass", text)
			self.assertIn("encrypted_password", text)
			self.assertNotIn("fixture-secret", text)
			self.assertNotIn("fixture-mail-secret", text)
			path = Path(directory) / "prime.ini"
			path.write_text(text)
			document = ConfigDocument(directory)
			result = save_configuration(document, form(document, ComputerID="fixture", email_username="new-mail-account"), "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(result["document"].config.get("PrimeNet", "encrypted_ProxyPass"), document.config.get("PrimeNet", "encrypted_ProxyPass"))
			self.assertEqual(result["document"].config.get("Email", "encrypted_password"), document.config.get("Email", "encrypted_password"))
			self.assertEqual(Path(result["backup"]).read_bytes(), document.data)
			self.assertNotIn("fixture-secret", result["document"].text)
			self.assertNotIn("fixture-mail-secret", result["document"].text)

	def test_backend_defaults_all_engines_without_side_effects(self):
		for engine in ("mlucas", "gpuowl", "prpll", "prmers", "cudalucas", "mfaktc", "mfakto", "primepath"):
			with self.subTest(engine=engine), tempfile.TemporaryDirectory() as directory:
				response = backend_request("validate_config", directory=directory, text="[PrimeNet]\nusername=ANONYMOUS\n{}=True\n".format(engine))
				self.assertEqual(response["num_workers"], 1)
				self.assertFalse(response["network_enabled"])
				self.assertFalse(response["configuration_written"])
				self.assertEqual(response["days_of_work"], 1 if engine in {"mfaktc", "mfakto", "primepath"} else 3)
				self.assertEqual(response["work_preferences"], [12 if engine in {"mfaktc", "mfakto", "primepath"} else 101 if engine == "cudalucas" else 150])
				self.assertEqual(list(Path(directory).iterdir()), [])

	def test_backend_rejects_conflicts_and_keeps_secret_out_of_response(self):
		for options in ("CertWork=True", "GetMinExponent=100\nGetMaxExponent=50", "convert_ll_to_prp=True\nconvert_prp_to_ll=True", "HoursBetweenCheckins=0"):
			with self.subTest(options=options), tempfile.TemporaryDirectory() as directory:
				text = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nProxyHost=localhost:8080\nProxyPass=secret-123\n" + options + "\n"
				with self.assertRaises(ControllerError) as caught:
					backend_request("validate_config", text=text, directory=directory)
				self.assertNotIn("secret-123", str(caught.exception))

	def test_effective_defaults_match_normal_offline_cli_status(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			text = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n"
			path.write_text(text)
			result = backend_request("validate_config", text=text, directory=directory)
			# The real entry point may write only inside this disposable directory.
			# An audit hook blocks Python socket network operations before startup.
			code = "import runpy,sys,gui_backend; sys.addaudithook(gui_backend._network_guard); sys.argv=['autoprimenet.py','--workdir',sys.argv[1],'--status','--timeout','0']; runpy.run_path('autoprimenet.py',run_name='__main__')"
			process = subprocess.run([sys.executable, "-B", "-c", code, directory], capture_output=True, text=True, timeout=30)
			self.assertEqual(process.returncode, 0, process.stderr)
			config = ConfigParser()
			config.optionxform = str
			config.read(path)
			self.assertEqual(config.getfloat("PrimeNet", "DaysOfWork"), result["days_of_work"])
			self.assertEqual(config.get("PrimeNet", "results_file"), result["results_file"])
			self.assertEqual(config.getint("PrimeNet", "WorkPreference"), result["work_preferences"][0])


if __name__ == "__main__":
	unittest.main()
