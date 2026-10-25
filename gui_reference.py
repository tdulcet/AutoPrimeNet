"""Explicit CLI-to-GUI coverage used by navigation and the parity inventory.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from gui_operations import OPERATIONS, operation_for_destination
from gui_options import field_for_destination


EXTRA = {
	"workdir": ("Settings", "Working directory selector", "Available"),
	"localfile": ("Settings", "Configuration filename", "Available"),
	"dirs": ("Workers", "Edit selected worker → Directory", "Available"),
	"work_preference": ("Workers", "Edit selected worker → Preference", "Available"),
	"num_workers": ("Workers", "Apply worker count", "Available"),
	"debug_info": ("Logs & Status", "Export private diagnostics", "Available"),
	"help": ("Advanced", "Original CLI help / searchable reference", "Available"),
	"version": ("Advanced", "Help → About", "Available"),
	"prime95": (None, "Hidden experimental Prime95 mode is not exposed", "Hidden / CLI only"),
	"password": (None, "Legacy account-password feature was removed upstream", "Removed upstream"),
}
for engine in ("mlucas", "gpuowl", "prpll", "prmers", "cudalucas", "mfaktc", "mfakto", "primepath"):
	EXTRA[engine] = ("Workers", "Computation program", "Available")


def reference_info(destination):
	field = field_for_destination(destination)
	if field:
		return field.tab, (field.dialog + " → " if field.dialog else "") + field.label, "Available"
	operation = operation_for_destination(destination)
	if operation:
		item = OPERATIONS[operation]
		return item.tab, item.title, "Available"
	if destination in {"email_password", "proxy_password"}:
		return "Notifications" if destination == "email_password" else "Settings", "Manage passwords (encrypted replacement)", "Available"
	return EXTRA.get(destination, (None, "No coverage classification", "Unmapped"))
