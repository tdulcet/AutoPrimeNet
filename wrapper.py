#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import division, print_function, unicode_literals

import sys

# Python 2
if hasattr(__builtins__, "raw_input"):
	input = raw_input

try:
	import autoprimenet
# except KeyboardInterrupt:
except SystemExit:
	if not sys.stdin.isatty() or not sys.stdout.isatty():
		raise
	print("\a")
	input("Hit Enter to exit: ")
	raise
except BaseException as e:
	if not sys.stdin.isatty() or not sys.stdout.isatty():
		raise
	print(
		"""
An error occurred: {}: {}
If you believe this is a bug with AutoPrimeNet, please create an issue: https://github.com/tdulcet/AutoPrimeNet/issues
""".format(type(e).__name__, e)
	)
	sys.excepthook(*sys.exc_info())
	# traceback.print_exc()
	print("\a")
	input("Hit Enter to exit: ")
	sys.exit(1)
