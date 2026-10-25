#!/usr/bin/env python3
"""Private native tray helper; communicate menu events over stdout.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import json
import sys
import threading


def emit(event):
	print(json.dumps({"event": event}), flush=True)


def main():
	if sys.platform not in {"darwin", "win32"}:
		emit("unavailable")
		return 1
	try:
		import pystray
		from PIL import Image, ImageDraw

		image = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
		draw = ImageDraw.Draw(image)
		draw.ellipse((6, 6, 58, 58), fill=(35, 97, 155, 255))
		draw.line((20, 44, 32, 19, 44, 44), fill="white", width=5)
		draw.line((25, 35, 39, 35), fill="white", width=4)
		state = ["Stopped"]
		icon = pystray.Icon(
			"autoprimenet-gui", image, "AutoPrimeNet GUI",
			menu=pystray.Menu(
				pystray.MenuItem("Open AutoPrimeNet GUI", lambda *_: emit("open"), default=True),
				pystray.MenuItem(lambda _item: "Scheduled monitoring: " + state[0], None, enabled=False),
				pystray.MenuItem("Start monitoring…", lambda *_: emit("start"), enabled=lambda _item: state[0] in {"Stopped", "Failed"}),
				pystray.MenuItem("Stop monitoring", lambda *_: emit("stop"), enabled=lambda _item: state[0] in {"Starting", "Running cycle", "Waiting", "Watching files"}),
				pystray.Menu.SEPARATOR,
				pystray.MenuItem("Quit AutoPrimeNet GUI", lambda *_: emit("quit")),
			),
		)
		stopping = threading.Event()

		def on_native_thread(function):
			if sys.platform == "darwin":
				from PyObjCTools import AppHelper
				AppHelper.callAfter(function)
			else:
				function()

		def wait_for_parent():
			# EOF is the shutdown signal. A crashed GUI also closes this pipe, so
			# an orphan menu-bar helper does not remain indefinitely.
			for line in sys.stdin:
				try:
					message = json.loads(line)
					if message.get("state") in {"Stopped", "Starting", "Running cycle", "Waiting", "Watching files", "Stopping", "Failed"}:
						state[0] = message["state"]
						on_native_thread(icon.update_menu)
				except (ValueError, AttributeError):
					continue
			stopping.set()
			on_native_thread(icon.stop)

		def setup(tray):
			def activate():
				if stopping.is_set():
					tray.stop()
					return
				tray.visible = True
				emit("ready")
			on_native_thread(activate)

		threading.Thread(target=wait_for_parent, daemon=True).start()
		icon.run(setup=setup)
		return 0
	except Exception:
		emit("unavailable")
		return 1


if __name__ == "__main__":
	sys.exit(main())
