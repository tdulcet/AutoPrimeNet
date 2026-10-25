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
		icon = pystray.Icon(
			"autoprimenet-gui", image, "AutoPrimeNet GUI — offline preview",
			menu=pystray.Menu(
				pystray.MenuItem("Open AutoPrimeNet GUI", lambda *_: emit("open"), default=True),
				pystray.MenuItem("Offline preview — monitoring unavailable", None, enabled=False),
				pystray.Menu.SEPARATOR,
				pystray.MenuItem("Quit AutoPrimeNet GUI", lambda *_: emit("quit")),
			),
		)
		stopping = threading.Event()

		def wait_for_parent():
			# EOF is the shutdown signal. A crashed GUI also closes this pipe, so
			# an orphan menu-bar helper does not remain indefinitely.
			for _line in sys.stdin:
				pass
			stopping.set()
			icon.stop()

		def setup(tray):
			if stopping.is_set():
				tray.stop()
				return
			tray.visible = True
			emit("ready")

		threading.Thread(target=wait_for_parent, daemon=True).start()
		icon.run(setup=setup)
		return 0
	except Exception:
		emit("unavailable")
		return 1


if __name__ == "__main__":
	sys.exit(main())
