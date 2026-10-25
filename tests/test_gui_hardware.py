"""GPU setup mapping and offline dispatch safety checks."""

from pathlib import Path
import unittest
from unittest.mock import patch

from gui_backend import _dispatch
from gui_hardware import gpu_settings


class HardwareTests(unittest.TestCase):
	def test_complete_gpu_uses_original_setup_units_and_memory_fraction(self):
		self.assertEqual(gpu_settings(("GPU", 20, 1500, 64, 2048, 8192, "ARCH=SM80", "CUDA")), {
			"CpuBrand": "GPU", "cpu_features": "ARCH=SM80", "CpuSpeed": "1500", "memory": "8192", "Memory": "7373",
			"NumCores": "20", "CpuNumHyperthreads": "1", "L1": "64", "L2": "2048", "L3": "0",
		})

	def test_nvml_unknown_cores_and_caches_retain_existing_overrides(self):
		values = gpu_settings(("GPU", None, 1000, None, None, 4096, "", "NVML"))
		self.assertFalse({"NumCores", "CpuNumHyperthreads", "L1", "L2", "L3"} & values.keys())
		self.assertEqual(values["Memory"], "3686")

	def test_bad_records_are_rejected(self):
		for record in ([], ("GPU", 1, float("nan"), 0, 0, 100, "", "CUDA"), ("GPU\n", 1, 2, 0, 0, 100, "", "CUDA"), ("GPU", -1, 2, 0, 0, 100, "", "CUDA")):
			with self.subTest(record=record), self.assertRaises(ValueError):
				gpu_settings(record)

	def test_dispatch_reuses_discovery_skips_unusable_devices_and_closes_session(self):
		from unittest.mock import Mock
		session = Mock()
		get_gpus = Mock(return_value=[("GPU", None, 1200, None, None, 2048, "", "NVML"), (None,) * 8])
		with patch("gui_backend._load_definitions", return_value={"get_gpus": get_gpus, "session": session}):
			result = _dispatch({"protocol": 1, "operation": "discover_gpus"}, Path(__file__).resolve().parents[1] / "autoprimenet.py")
		get_gpus.assert_called_once_with()
		session.close.assert_called_once_with()
		self.assertEqual(len(result["devices"]), 1)
		self.assertEqual(result["devices"][0]["source"], "NVML")
		self.assertFalse(result["network_enabled"])
		self.assertFalse(result["files_written"])
