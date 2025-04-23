#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Read Prime95/MPrime, Mlucas, GpuOwl/PRPLL, CUDALucas, CUDAPm1, mfaktc and mfakto save/checkpoint and proof files, and display status of them."""

# Adapted from: https://github.com/sethtroisi/prime95/blob/py_status_report/prime95_status.py

# Copyright (c) 2021-2024 Seth Troisi and Teal Dulcet
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, version 3.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.

from __future__ import division, print_function, unicode_literals

import binascii
import ctypes
import glob
import hashlib
import json
import locale
import logging
import math
import optparse
import os
import re
import struct
import sys
import timeit
from ctypes.util import find_library
from datetime import datetime, timedelta

try:
	# Python 2
	from future_builtins import map, zip  # ascii, filter, hex, oct
except ImportError:
	pass

if sys.version_info >= (3, 7):
	# Python 3.7+
	OrderedDict = dict
else:
	try:
		# Python 2.7 and 3.1+
		from collections import OrderedDict
	except ImportError:
		OrderedDict = dict

try:
	# Python 3.3+
	from math import log2
except ImportError:

	def log2(x):
		"""Calculate the base-2 logarithm of a given number."""
		return math.log(x, 2)


if sys.platform != "win32":
	libc = ctypes.CDLL(find_library("c"))
	libc.wcswidth.argtypes = (ctypes.c_wchar_p, ctypes.c_int)
	libc.wcswidth.restype = ctypes.c_int

	def wcswidth(astr):
		"""Returns the number of columns needed to display the given wide-character string."""
		return libc.wcswidth(astr, len(astr))

else:
	# Only supports ASCII characters on Windows
	# Would need the wcwidth library to support Unicode characters
	# from wcwidth import wcswidth
	wcswidth = len


try:
	# Python 3.2+
	import concurrent.futures
except ImportError:
	executor = None
else:
	import multiprocessing

	executor = concurrent.futures.ThreadPoolExecutor(multiprocessing.cpu_count())


locale.setlocale(locale.LC_ALL, "")
# Python 2
if hasattr(__builtins__, "unicode"):
	str = unicode

# Python 2
if hasattr(__builtins__, "xrange"):
	range = xrange

# Prime95/MPrime constants

CERT_MAGICNUM = 0x8F729AB1
FACTOR_MAGICNUM = 0x1567234D
LL_MAGICNUM = 0x2C7330A8
PRP_MAGICNUM = 0x87F2A91B
ECM_MAGICNUM = 0x1725BCD9
PM1_MAGICNUM = 0x317A394B
PP1_MAGICNUM = 0x912A374A

CERT_VERSION = 1
FACTOR_VERSION = 1
LL_VERSION = 1
PRP_VERSION = 7
ECM_VERSION = 6
PM1_VERSION = 8
PP1_VERSION = 2

# Mlucas constants

TEST_TYPE_PRIMALITY = 1
TEST_TYPE_PRP = 2
TEST_TYPE_PM1 = 3

MODULUS_TYPE_MERSENNE = 1
# MODULUS_TYPE_MERSMERS = 2
MODULUS_TYPE_FERMAT = 3
# MODULUS_TYPE_GENFFTMUL = 4

# GpuOwl headers

# Exponent, iteration, 0, hash
# HEADER_v1 = "OWL LL 1 %u %u 0 %" SCNx64 "\n"
LL_v1_RE = re.compile(br"^OWL LL (1) (\d+) (\d+) 0 ([\da-f]+)$")

# E, k, CRC
# LL_v1 = "OWL LL 1 E=%u k=%u CRC=%u\n"
LL_v1a_RE = re.compile(br"^OWL LL (1) E=(\d+) k=(\d+) CRC=(\d+)$")

# # OWL 1 <exponent> <iteration> <width> <height> <sum> <nErrors>
# # HEADER = "OWL 1 %d %d %d %d %d %d\n"

# # OWL 2 <exponent> <iteration> <nErrors>
# # HEADER = "OWL 2 %d %d %d\n"

# # <exponent> <iteration> <nErrors> <check-step>
# # HEADER = "OWL 3 %d %d %d %d\n"
# # HEADER = "OWL 3 %u %u %d %u\n"

# # <exponent> <iteration> <nErrors> <check-step> <checksum>
# # HEADER = "OWL 4 %d %d %d %d %016llx\n"
# # HEADER = "OWL 4 %u %u %d %u %016llx\n"

# # HEADER_R = R"(OWL 5
# # Comment: %255[^
# # ]
# # Type: PRP
# # Exponent: %d
# # Iteration: %d
# # PRP-block-size: %d
# # Residue-64: 0x%016llx
# # Errors: %d
# # End-of-header:
# # \0)";
# # HEADER_R = R"(OWL 5
# # Comment: %255[^
# # ]
# # Type: PRP
# # Exponent: %u
# # Iteration: %u
# # PRP-block-size: %u
# # Residue-64: 0x%016llx
# # Errors: %d
# # End-of-header:
# # \0)";

# # Exponent, iteration, block-size, res64, nErrors.
# # HEADER = "OWL PRP 6 %u %u %u %016llx %d\n"
# # HEADER = "OWL PRP 6 %u %u %u %016llx %u\n"

# # E, k, B1, blockSize, res64
# # HEADER = "OWL PRPF 1 %u %u %u %u %016llx\n"

# # Exponent, iteration, B1, block-size, res64.
# # HEADER_v7 = "OWL PRP 7 %u %u %u %u %016llx\n"

# # Exponent, iteration, B1, block-size, res64, stage, nBitsBase
# # HEADER_v8 = "OWL PRP 8 %u %u %u %u %016llx %u %u\n"

# Exponent, iteration, block-size, res64
# HEADER_v9  = "OWL PRP 9 %u %u %u %016llx\n"
PRP_v9_RE = re.compile(br"^OWL PRP (9) (\d+) (\d+) (\d+) ([\da-f]{16})$")

# E, k, block-size, res64, nErrors
# PRP_v10 = "OWL PRP 10 %u %u %u %016" SCNx64 " %u\n"
PRP_v10_RE = re.compile(br"^OWL PRP (10) (\d+) (\d+) (\d+) ([\da-f]{16}) (\d+)$")

# Exponent, iteration, block-size, res64, nErrors
# HEADER_v11 = "OWL PRP 11 %u %u %u %016" SCNx64 " %u\n"
# Exponent, iteration, block-size, res64, nErrors, B1, nBits, start, nextK, crc
# PRP_v11 = "OWL PRP 11 %u %u %u %016" SCNx64 " %u %u %u %u %u %u\n"
PRP_v11_RE = re.compile(br"^OWL PRP (11) (\d+) (\d+) (\d+) ([\da-f]{16}) (\d+)(?: (\d+) (\d+) (\d+) (\d+) (\d+))?$")

# E, k, block-size, res64, nErrors, CRC
# PRP_v12 = "OWL PRP 12 %u %u %u %016" SCNx64 " %u %u\n"
PRP_v12_RE = re.compile(br"^OWL PRP (12) (\d+) (\d+) (\d+) ([\da-f]{16}) (\d+) (\d+)$")

# # Exponent, iteration, total-iterations, B1.
# # HEADER = "OWL PF 1 %u %u %u %u\n"

# # Exponent, iteration, B1.
# # HEADER = "OWL P-1 1 %u %u %u

# Exponent, B1, iteration, nBits
# HEADER_v1 = "OWL PM1 1 %u %u %u %u\n"
# HEADER_v1 = "OWL P1 1 %u %u %u %u\n"
P1_v1_RE = re.compile(br"^OWL PM?1 (1) (\d+) (\d+) (\d+) (\d+)$")

# E, B1, k, nextK, CRC
# P1_v2 = "OWL P1 2 %u %u %u %u %u\n"
P1_v2_RE = re.compile(br"^OWL P1 (2) (\d+) (\d+) (\d+) (\d+) (\d+)$")

# P1_v3 = "OWL P1 3 E=%u B1=%u k=%u block=%u\n"
# P1_v3 = "OWL P1 3 E=%u B1=%u k=%u\n"
P1_v3_RE = re.compile(br"^OWL P1 (3) E=(\d+) B1=(\d+) k=(\d+)(?: block=(\d+))?$")

# E, B1, CRC
# P1Final_v1 = "OWL P1F 1 %u %u %u\n"
P1Final_v1_RE = re.compile(br"^OWL P1F (1) (\d+) (\d+) (\d+)$")

# Exponent, B1, B2, nWords, kDone
# HEADER_v1 = "OWL P2 1 %u %u %u %u 2880 %u\n"
P2_v1_RE = re.compile(br"^OWL P2 (1) (\d+) (\d+) (\d+) (\d+) 2880 (\d+)$")

# E, B1, B2, CRC
# P2_v2 = "OWL P2 2 %u %u %u %u\n"
# E, B1, B2
# P2_v2 = "OWL P2 2 %u %u %u\n"
P2_v2_RE = re.compile(br"^OWL P2 (2) (\d+) (\d+) (\d+)(?: (\d+))?$")

# E, B1, B2, D, nBuf, nextBlock
# P2_v3 = "OWL P2 3 %u %u %u %u %u %u\n"
P2_v3_RE = re.compile(br"^OWL P2 (3) (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)$")

# # Exponent, bitLo, classDone, classTotal.
# # HEADER = "OWL TF 1 %d %d %d %d\n"

# # Exponent, bitLo, bitHi, classDone, classTotal.
# # HEADER = "OWL TF 2 %d %d %d %d %d\n"
# # HEADER = "OWL TF 2 %u %d %d %d %d\n"
# # HEADER = "OWL TF 2 %u %u %u %u %u\n"
TF_v2_RE = re.compile(br"^OWL TF (2) (\d+) (\d+) (\d+) (\d+) (\d+)$")

# mfaktc/mfakto headers

# "%s%u %d %d %d %s: %d %d %s %llu %08X", NAME_NUMBERS, exp, bit_min, bit_max, NUM_CLASSES, MFAKTC_VERSION, cur_class, num_factors, strlen(factors_string) ? factors_string : "0", bit_level_time, i
MFAKTC_TF_RE = re.compile(
	br'^([MW])(\d+) (\d+) (\d+) (\d+) ([^\s:]+): (\d+) (\d+) (?:(0|"\d+"(?:,"\d+")*|\d+(?:,\d+)*) (\d+) )?([\dA-F]{8})$'
)

# "%u %d %d %d %s: %d %d %s %llu %08X\n", exp, bit_min, bit_max, mystuff.num_classes, MFAKTO_VERSION, cur_class, num_factors, strlen(factors_string) ? factors_string : "0", bit_level_time, i
MFAKTO_TF_RE = re.compile(br'^(\d+) (\d+) (\d+) (\d+) (mfakto [^\s:]+): (\d+) (\d+) (?:(0|"\d+"(?:,"\d+")*) (\d+) )?([\dA-F]{8})$')

PROOF_NUMBER_RE = re.compile(br"^(\()?([MF]?(\d+)|(?:(\d+)\*)?(\d+)\^(\d+)([+-]\d+))(?(1)\))(?:/(\d+(?:/\d+)*))?$")

# PRPLL headers

# LL_v13 = "OWL LL 13 N=1*2^%u-1 k=%u time=%lf\n"
LL_v13_RE = re.compile(br"^OWL LL (13) N=1\*2\^(\d+)-1 k=(\d+) time=(\d+(?:\.\d+)?)$")

# PRP_v13 = "OWL PRP 13 N=1*2^%u-1 k=%u block=%u res64=%016" SCNx64 " err=%u time=%lf\n"
PRP_v13_RE = re.compile(br"^OWL PRP (13) N=1\*2\^(\d+)-1 k=(\d+) block=(\d+) res64=([\da-f]{16}) err=(\d+) time=(\d+(?:\.\d+)?)$")


PRIME95_RE = re.compile(
	r"^[pfemnc](?:[0-9]{2}[B-T][0-9]{4}|[0-9][A-Z][0-9]{5}|[A-Y][0-9]{6}|[0-9]+)(?:_[0-9]+){0,2}(?:\.(?:[0-9]{3,}|(bu([0-9]*))|bad[0-9]+))?$"
)
MLUCAS_RE = re.compile(r"^([pfq])([0-9]+)(?:\.(?:s([12])|([0-9]+)M|G))?$")
CUDALUCAS_RE = re.compile(r"^([ct])([0-9]+)$")
CUDAPM1_RE = re.compile(r"^([ct])([0-9]+)s([12])$")
GPUOWL_RE = re.compile(
	r"(?:(?:ll-)?([0-9]+)"
	+ re.escape(os.sep)
	+ r"(?:([0-9]+)(?:-([0-9]+)\.(?:ll|prp|p1final|p2)|(?:-[0-9]+-([0-9]+))?\.p1|(-old)?\.(?:(?:ll|p[12])\.)?owl)|unverified\.prp(\.bak)?)|[0-9]+(-prev)?\.(?:tf\.)?owl)$"
)
PRPLL_RE = re.compile(r"(?:(?:ll-)?([0-9]+)" + re.escape(os.sep) + r"(?:([0-9]+)-([0-9]+)\.(?:ll|prp)|unverified\.prp))$")
MFAKTC_RE = re.compile(r"^([MW][0-9]+)(?:_[0-9]+-[0-9]+_[0-9]+)?\.ckp$")
MFAKTO_RE = re.compile(r"^(M[0-9]+)\.ckp(\.bu)?$")


# Enum
class scale:
	"""Enumeration for different scaling systems."""

	SI = 0
	IEC = 1
	IEC_I = 2


suffix_power_char = ("", "K", "M", "G", "T", "P", "E", "Z", "Y", "R", "Q")

WORK_FACTOR = 0
WORK_TEST = 1
# WORK_DBLCHK = 2
# WORK_ADVANCEDTEST = 3
WORK_ECM = 4
WORK_PMINUS1 = 5
WORK_PPLUS1 = 6
# WORK_PFACTOR = 7
WORK_PRP = 10
WORK_CERT = 11

PRP_STATE_NORMAL = 0
PRP_STATE_DCHK_PASS1 = 10
PRP_STATE_DCHK_PASS2 = 11
PRP_STATE_GERB_START_BLOCK = 22
PRP_STATE_GERB_MID_BLOCK = 23
PRP_STATE_GERB_MID_BLOCK_MULT = 24
PRP_STATE_GERB_END_BLOCK = 25
PRP_STATE_GERB_END_BLOCK_MULT = 26
PRP_STATE_GERB_FINAL_MULT = 27

ECM_STATE_STAGE1_INIT = 0
ECM_STATE_STAGE1 = 1
ECM_STATE_MIDSTAGE = 2
ECM_STATE_STAGE2 = 3
ECM_STATE_GCD = 4

ECM_STAGE2_PAIRING = 0
ECM_STAGE2_POLYMULT = 1

ECM_STATES = ("Stage 1 Init", "Stage 1", "Midstage", "Stage 2", "GCD")
ECM_SIGMA_TYPES = ("Edwards", "Montgomery", "", "GMP-ECM param3")

PM1_STATE_STAGE0 = 0
PM1_STATE_STAGE1 = 1
PM1_STATE_MIDSTAGE = 2
PM1_STATE_STAGE2 = 3
PM1_STATE_GCD = 4
PM1_STATE_DONE = 5

PM1_STAGE2_PAIRING = 0
PM1_STAGE2_POLYMULT = 1

PM1_STATES = ("Stage 0", "Stage 1", "Midstage", "Stage 2", "GCD", "Done")

PP1_STATE_STAGE1 = 1
PP1_STATE_MIDSTAGE = 2
PP1_STATE_STAGE2 = 3
PP1_STATE_GCD = 4
PP1_STATE_DONE = 5

PP1_STATES = ("", "Stage 1", "Midstage", "Stage 2", "GCD", "Done")


class work_unit(object):
	"""Represents a work unit for GIMPS computations."""

	__slots__ = (
		"work_type",
		"k",
		"b",
		"n",
		"c",
		"known_factors",
		"stage",
		"pct_complete",
		"fftlen",
		"nerr_roe",
		"nerr_gcheck",
		"error_count",
		"counter",
		"shift_count",
		"res64",
		"res35m1",
		"res36m1",
		"total_time",
		"factor_found",
		"bits",
		"apass",
		"test_bits",
		"num_factors",
		"prp_base",
		"residue_type",
		"L",
		"proof_power",
		"isProbablePrime",
		"res2048",
		"proof_power_mult",
		"proof_version",
		"curve",
		"state",
		"B",
		"stage1_prime",
		"C",
		"sigma",
		"sigma_type",
		"D",
		"B2_start",
		"B_done",
		"interim_B",
		"C_done",
		"interim_C",
		"stage0_bitnum",
		"E",
		"numerator",
		"denominator",
		"version",
		"jacobi",
	)

	def __init__(self, work_type=None):
		"""Initializes a new work unit with optional work type."""
		self.work_type = work_type
		# k*b^n+c
		self.k = 1.0
		self.b = 2
		self.n = 0
		self.c = -1
		self.known_factors = None
		self.fftlen = None
		self.nerr_roe = None
		self.nerr_gcheck = None
		self.error_count = None
		self.counter = None
		self.shift_count = None
		self.res64 = None
		self.res35m1 = None
		self.res36m1 = None
		self.total_time = None
		self.version = None

		# Factor
		self.factor_found = None
		self.test_bits = None
		self.num_factors = None

		# PRP
		self.prp_base = None
		self.residue_type = None
		self.L = None
		self.proof_power = None
		self.isProbablePrime = None
		self.res2048 = None
		self.proof_power_mult = None
		self.proof_version = None

		# ECM
		self.C = None
		self.D = None
		self.B2_start = None

		# P-1
		self.B_done = None
		self.interim_B = None
		self.C_done = None
		self.interim_C = None
		self.stage0_bitnum = None
		self.E = None


# CUDALucas, mfaktc and mfakto use a "CRC-32 like checksum", so binascii.crc32() cannot be used
crc32_table = []
for i in range(256):
	crc = i << 24
	for _j in range(8):
		if crc & 0x80000000:
			crc = (crc << 1) ^ 0x04C11DB7
		else:
			crc <<= 1
	crc32_table.append(crc & 0xFFFFFFFF)


def checkpoint_checksum(buffer):
	"""Calculate a CRC-32 like checksum for the given buffer."""
	chksum = 0
	for b in bytearray(buffer):
		chksum = ((chksum << 8) ^ crc32_table[(chksum >> 24) ^ b]) & 0xFFFFFFFF
	return chksum


# Adapted from: https://github.com/tdulcet/Distributed-Computing-Scripts/blob/master/primenet.py
def exponent_to_str(assignment):
	"""Converts an assignment's exponent details into a formatted string representation."""
	if not assignment.n:
		buf = "{0:.0f}".format(assignment.k + assignment.c)
	elif assignment.k != 1.0:
		buf = "{0.k:.0f}*{0.b}^{0.n}{0.c:+}".format(assignment)
	elif assignment.b == 2 and assignment.c == -1:
		buf = "M{0.n}".format(assignment)
	else:
		cnt = 0
		temp_n = assignment.n
		while not temp_n & 1:
			temp_n >>= 1
			cnt += 1
		if assignment.b == 2 and temp_n == 1 and assignment.c == 1:
			buf = "F{0}".format(cnt)
		else:
			buf = "{0.b}^{0.n}{0.c:+}".format(assignment)
	return buf


def assignment_to_str(assignment):
	"""Converts an assignment object to its string representation, including known factors if present."""
	buf = exponent_to_str(assignment)
	if not assignment.known_factors:
		return buf
	return "{0}/{1}".format("({0})".format(buf) if "^" in buf else buf, "/".join(map(str, assignment.known_factors)))


def strcol(astr):
	"""Returns the display width of a string, raising an error if it contains nonprintable wide characters."""
	width = wcswidth(astr)
	if width == -1:
		msg = "wcswidth failed. Nonprintable wide character."
		raise ValueError(msg)
	return width


def output_table(rows):
	"""Formats and prints a table from a list of rows with aligned columns."""
	amax = max(map(len, rows))
	for row in rows:
		row.extend("" for _ in range(amax - len(row)))
	lens = [max(map(strcol, col)) for col in zip(*rows)]
	print(
		"\n".join(
			"  ".join("{{{0}:<{1}}}".format(i, alen - (strcol(v) - len(v))) for i, (alen, v) in enumerate(zip(lens, row))).format(
				*row
			)
			for row in rows
		)
	)


# Adapted from: https://github.com/tdulcet/Table-and-Graph-Libs/blob/master/python/graphs.py
def outputunit(number, ascale=scale.IEC_I):
	"""Converts a number to a human-readable string with appropriate unit suffix based on the given scale."""
	if ascale in {scale.IEC, scale.IEC_I}:
		scale_base = 1024
	elif ascale == scale.SI:
		scale_base = 1000

	power = 0
	while abs(number) >= scale_base:
		power += 1
		number /= scale_base

	anumber = abs(number)
	anumber += 0.0005 if anumber < 10 else 0.005 if anumber < 100 else 0.05 if anumber < 1000 else 0.5

	if number and anumber < 1000 and power > 0:
		strm = "{0:.{prec}g}".format(number, prec=sys.float_info.dig)

		length = 5 + (number < 0)
		if len(strm) > length:
			prec = 3 if anumber < 10 else 2 if anumber < 100 else 1
			strm = "{0:.{prec}f}".format(number, prec=prec)
	else:
		strm = "{0:.0f}".format(number)

	# "k" if power == 1 and ascale == scale.SI else
	strm += " " + (suffix_power_char[power] if power < len(suffix_power_char) else "(error)")

	if ascale == scale.IEC_I and power > 0:
		strm += "i"

	return strm


# Python 3.2+
if hasattr(int, "to_bytes"):

	def to_bytes(n, length=1, byteorder="little"):
		"""Convert an integer to a bytes object of specified length and byte order."""
		return n.to_bytes(length, byteorder)

else:

	def to_bytes(n, length=1, byteorder="little"):
		"""Convert an integer to a bytes object of specified length and byte order."""
		if byteorder == "little":
			order = range(length)
		elif byteorder == "big":
			order = reversed(range(length))

		return bytes(bytearray((n >> i * 8) & 0xFF for i in order))


gmp_lib = find_library("libgmp" if sys.platform == "win32" else "gmp")
if gmp_lib:
	gmp = ctypes.CDLL(gmp_lib)

	class mpz_t(ctypes.Structure):
		_fields_ = (("mp_alloc", ctypes.c_int), ("mp_size", ctypes.c_int), ("mp_d", ctypes.POINTER(ctypes.c_ulong)))

	def mpz_import(value, mpz):
		"""Imports an integer value into a GMP mpz_t type."""
		abytes = to_bytes(value, -(value.bit_length() // -8))
		gmp.__gmpz_import(ctypes.byref(mpz), len(abytes), -1, 1, 0, 0, abytes)

	def jacobi(a, n):
		"""Calculate the Jacobi symbol (a/n) using GMP library functions."""
		a_mpz = mpz_t()
		n_mpz = mpz_t()

		gmp.__gmpz_init(ctypes.byref(a_mpz))
		gmp.__gmpz_init(ctypes.byref(n_mpz))

		try:
			mpz_import(a, a_mpz)
			mpz_import(n, n_mpz)

			return gmp.__gmpz_jacobi(ctypes.byref(a_mpz), ctypes.byref(n_mpz))
		finally:
			gmp.__gmpz_clear(ctypes.byref(a_mpz))
			gmp.__gmpz_clear(ctypes.byref(n_mpz))

else:
	# Adapted from: https://rosettacode.org/wiki/Jacobi_symbol#Python
	def jacobi(a, n):
		"""Compute the Jacobi symbol (a/n) for given integers a and n."""
		if n <= 0:
			msg = "'n' must be a positive integer."
			raise ValueError(msg)
		if not n & 1:
			msg = "'n' must be odd."
			raise ValueError(msg)
		a %= n
		result = 1
		while a:
			while not a & 1:
				a >>= 1
				if n & 7 in {3, 5}:
					result = -result
			a, n = n, a
			if a & 3 == n & 3 == 3:
				result = -result
			a %= n
		return result if n == 1 else 0


def jacobi_test(wu, p, words, filename):
	"""Performs a Jacobi error check on the given work unit."""
	logging.debug("%r: Performing Jacobi Error Check, this may take a while…", filename)
	start = timeit.default_timer()
	wu.jacobi = jacobi(words - 2, (1 << p) - 1)
	end = timeit.default_timer()
	logging.info(
		"%r: Jacobi: %s (%s), Time: %.1f ms", filename, wu.jacobi, "Passed" if wu.jacobi == -1 else "Failed", (end - start) * 1000
	)
	# return wu.jacobi


# Python 3.2+
if hasattr(int, "from_bytes"):

	def from_bytes(abytes, byteorder="little"):
		"""Convert a byte sequence to an integer using the specified byte order."""
		return int.from_bytes(abytes, byteorder)

else:

	def from_bytes(abytes, byteorder="little"):
		"""Convert a byte sequence to an integer using the specified byte order."""
		if byteorder == "big":
			abytes = reversed(abytes)
		return sum(b << i * 8 for i, b in enumerate(bytearray(abytes)))


def rotr(value, count, p, n):
	"""Performs a bitwise right rotation on a given value."""
	return (value >> count) | (value << (p - count) & n)


def unpack(aformat, file, noraise=False):
	"""Unpacks binary data from a file according to the specified format."""
	size = struct.calcsize(aformat)
	buffer = file.read(size)
	if len(buffer) != size:
		if noraise and not buffer:
			return None
		raise EOFError
	return struct.unpack(aformat, buffer)


def read_value_prime95(file, aformat, asum):
	"""Read a value from a Prime95 work unit file and update the checksum."""
	result = unpack(aformat, file)
	if options.check:
		for char, val in zip(aformat[1:], result):
			if char == "i":
				asum += val
			elif char == "I":
				asum += val
			elif char == "Q":
				asum += (val >> 32) + val
			elif char == "d":
				asum += int(val) & 0xFFFFFFFF
	return result, asum


def read_array_prime95(file, size, asum):
	"""Read an array from a Prime95 work unit file and update the checksum."""
	buffer = file.read(size)
	if len(buffer) != size:
		raise EOFError
	if options.check:
		asum += sum(bytearray(buffer))
	return buffer, asum


def read_residue_prime95(file, asum):
	"""Read a residue from a Prime95 work unit file and update the checksum."""
	(alen,), asum = read_value_prime95(file, "<I", asum)

	aformat = "<{0}I".format(alen)
	size = struct.calcsize(aformat)
	buffer = file.read(size)
	if len(buffer) != size:
		raise EOFError
	if options.check:
		# result = array("I", buffer)
		result = struct.unpack(aformat, buffer)
		asum += alen
		asum += sum(result)
	return buffer, asum


def parse_work_unit_prime95(filename):
	"""Parses a Prime95 work unit file, extracting important information."""
	wu = work_unit()

	try:
		with open(filename, "rb") as f:
			magicnum, wu.version, wu.k, wu.b, wu.n, wu.c, stage, pct_complete, filesum = unpack("<IIdIIi10sxxdI", f)

			wu.stage = stage.rstrip(b"\0").decode()
			wu.pct_complete = max(0, min(1, pct_complete))

			if options.check or options.jacobi:
				bit_len = int(math.ceil(log2(wu.k) + wu.n * log2(wu.b)))

			asum = 0

			if magicnum == CERT_MAGICNUM:
				if wu.version != CERT_VERSION:
					logging.error("Cert savefile with unsupported version = %s", wu.version)
					return None

				wu.work_type = WORK_CERT

				(wu.error_count, wu.counter, wu.shift_count), asum = read_value_prime95(f, "<III", asum)

				if options.check:
					residue, asum = read_residue_prime95(f, asum)
					residue = rotr(from_bytes(residue), wu.shift_count, bit_len, (1 << bit_len) - 1)
					wu.res64 = "{0:016X}".format(residue & 0xFFFFFFFFFFFFFFFF)
					wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)
			elif magicnum == FACTOR_MAGICNUM:
				if wu.version != FACTOR_VERSION:
					logging.error("Factor with unsupported version = %s", wu.version)
					return None

				wu.work_type = WORK_FACTOR

				wu.factor_found, wu.bits, wu.apass, _fachsw, _facmsw, _endpthi, _endptlo = unpack("<IIIIIII", f)
			elif magicnum == LL_MAGICNUM:
				if wu.version != LL_VERSION:
					logging.error("LL savefile with unsupported version = %s", wu.version)
					return None

				wu.work_type = WORK_TEST

				(wu.error_count, wu.counter, wu.shift_count), asum = read_value_prime95(f, "<III", asum)

				if options.check or options.jacobi:
					residue, asum = read_residue_prime95(f, asum)
					residue = rotr(from_bytes(residue), wu.shift_count, bit_len, (1 << bit_len) - 1)
					wu.res64 = "{0:016X}".format(residue & 0xFFFFFFFFFFFFFFFF)
					wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)
				if options.jacobi:
					if executor:
						executor.submit(jacobi_test, wu, wu.n, residue, filename)
					else:
						jacobi_test(wu, wu.n, residue, filename)
			elif magicnum == PRP_MAGICNUM:
				if not 1 <= wu.version <= PRP_VERSION:
					logging.error("PRP savefile with unsupported version = %s", wu.version)
					return None

				wu.work_type = WORK_PRP

				(wu.error_count, wu.counter), asum = read_value_prime95(f, "<II", asum)

				if wu.version >= 2:
					(wu.prp_base, wu.shift_count, _two_power_opt), asum = read_value_prime95(f, "<III", asum)
				else:
					wu.prp_base = 3
					wu.shift_count = 0

				if wu.version >= 3:
					(
						(
							wu.residue_type,
							_error_check_type,
							wu.state,
							_alt_shift_count,
							wu.L,
							_start_counter,
							_next_mul_counter,
							_end_counter,
						),
						asum,
					) = read_value_prime95(f, "<IIIIIIII", asum)
				else:
					wu.state = PRP_STATE_NORMAL

				if wu.version >= 5:
					(wu.proof_power, _hashlen, wu.isProbablePrime, _have_res2048), asum = read_value_prime95(f, "<IIII", asum)
					res2048, asum = read_array_prime95(f, 512, asum)
					wu.res2048 = res2048.rstrip(b"\0").decode()
					res64, asum = read_array_prime95(f, 16, asum)
					wu.res64 = res64.rstrip(b"\0").decode()
				else:
					wu.proof_power = 0

				if wu.version >= 6:
					(wu.proof_power_mult, _md5_residues), asum = read_value_prime95(f, "<II", asum)
				else:
					wu.proof_power_mult = 1

				if wu.version >= 7:
					(wu.proof_version,), asum = read_value_prime95(f, "<I", asum)
				else:
					wu.proof_version = 1

				if options.check:
					residue, asum = read_residue_prime95(f, asum)
					residue = rotr(from_bytes(residue), wu.shift_count, bit_len, (1 << bit_len) - 1)
					ares64 = residue & 0xFFFFFFFFFFFFFFFF
					if wu.res64:
						res64 = int(res64, 16)
						if res64 != ares64:
							logging.error("Res64 error. Expected %X, actual %X.", res64, ares64)
					else:
						wu.res64 = "{0:016X}".format(ares64)
					ares2048 = residue & (1 << 2048) - 1
					if wu.res2048:
						res2048 = int(res2048, 16)
						if res2048 != ares2048:
							logging.error("Res2048 error. Expected %X, actual %X.", res2048, ares2048)
					else:
						wu.res2048 = "{0:0512X}".format(ares2048)

					if wu.version == 3 and wu.state == PRP_STATE_GERB_START_BLOCK:
						_alt_shift_count = wu.shift_count
					elif wu.state not in {PRP_STATE_NORMAL, PRP_STATE_GERB_MID_BLOCK, PRP_STATE_GERB_MID_BLOCK_MULT}:
						_alt_residue, asum = read_residue_prime95(f, asum)
						# _alt_residue = from_bytes(_alt_residue)

					if wu.state not in {
						PRP_STATE_NORMAL,
						PRP_STATE_DCHK_PASS1,
						PRP_STATE_DCHK_PASS2,
						PRP_STATE_GERB_START_BLOCK,
						PRP_STATE_GERB_FINAL_MULT,
					}:
						_u0, asum = read_residue_prime95(f, asum)

					if wu.state not in {PRP_STATE_NORMAL, PRP_STATE_DCHK_PASS1, PRP_STATE_DCHK_PASS2, PRP_STATE_GERB_START_BLOCK}:
						_d, asum = read_residue_prime95(f, asum)
			elif magicnum == ECM_MAGICNUM:
				if not 1 <= wu.version <= ECM_VERSION:
					logging.error("ECM savefile with unsupported version = %s", wu.version)
					return None

				wu.work_type = WORK_ECM

				if wu.version == 1:  # 25 - 30.6
					(wu.state, wu.curve), asum = read_value_prime95(f, "<II", asum)

					(wu.sigma,) = unpack("<d", f)

					(wu.B, wu.stage1_prime, _C_processed), asum = read_value_prime95(f, "<QQQ", asum)

					wu.sigma_type = 1

					if options.check:
						_x, asum = read_residue_prime95(f, asum)

						_z, asum = read_residue_prime95(f, asum)
				else:
					(wu.curve,), asum = read_value_prime95(f, "<I", asum)

					(_average_B2,) = unpack("<Q", f)

					(wu.state,), asum = read_value_prime95(f, "<I", asum)

					(wu.sigma,) = unpack("<d" if wu.version < 5 else "<Q", f)

					(wu.B, wu.C), asum = read_value_prime95(f, "<QQ", asum)

					if wu.version < 6:
						wu.sigma_type = 1
						montg_stage1 = True
					else:
						(wu.sigma_type, montg_stage1), asum = read_value_prime95(f, "<II", asum)

					if wu.version <= 3:
						if wu.state == ECM_STATE_STAGE1:
							(wu.stage1_prime,), asum = read_value_prime95(f, "<Q", asum)
						elif wu.state == ECM_STATE_MIDSTAGE:
							pass
						elif wu.state == ECM_STATE_STAGE2:
							(
								(
									_stage2_numvals,
									totrels,
									wu.D,
									_E,
									_TWO_FFT_STAGE2,
									_pool_type,
									_first_relocatable,
									_last_relocatable,
									wu.B2_start,
									_C_done,
									numDsections,
									Dsection,
								),
								asum,
							) = read_value_prime95(f, "<IIIIIIQQQQQQ", asum)
							if wu.version == 2:
								(bitarraymaxDsections, bitarrayfirstDsection), asum = read_value_prime95(f, "<QQ", asum)

								bitarray_numDsections = min(numDsections - bitarrayfirstDsection, bitarraymaxDsections)
								bitarray_len = -((bitarray_numDsections * totrels) // -8)
								bitarray_start = ((Dsection - bitarrayfirstDsection) * totrels) // 8
								_bitarray, asum = read_array_prime95(f, bitarray_len - bitarray_start, asum)
							else:
								(_max_pairmap_Dsections, _relp), asum = read_value_prime95(f, "<QI", asum)

								_relp_sets, asum = read_array_prime95(f, 32 * 2, asum)

								(pairmap_size,), asum = read_value_prime95(f, "<Q", asum)

								_pairmap, asum = read_array_prime95(f, pairmap_size, asum)
						elif wu.state == ECM_STATE_GCD:
							pass

						if options.check:
							_x, asum = read_residue_prime95(f, asum)

							_z, asum = read_residue_prime95(f, asum)
					else:
						if wu.state == ECM_STATE_STAGE1:
							if montg_stage1:
								(wu.stage1_prime,), asum = read_value_prime95(f, "<Q", asum)

								if options.check:
									_x, asum = read_residue_prime95(f, asum)

									_z, asum = read_residue_prime95(f, asum)
							else:
								(_stage1_start_prime, _stage1_exp_buffer_size, _stage1_bitnum, _NAF_dictionary_size), asum = (
									read_value_prime95(f, "<QIII", asum)
								)

								if options.check:
									_x, asum = read_residue_prime95(f, asum)

									_y, asum = read_residue_prime95(f, asum)

									_x, asum = read_residue_prime95(f, asum)

									_y, asum = read_residue_prime95(f, asum)

									_z, asum = read_residue_prime95(f, asum)
						elif wu.state == ECM_STATE_MIDSTAGE:
							if options.check:
								_Qx_binary, asum = read_residue_prime95(f, asum)

								(tmp,), asum = read_value_prime95(f, "<i", asum)

								if tmp:
									_Qz_binary, asum = read_residue_prime95(f, asum)

								(tmp,), asum = read_value_prime95(f, "<i", asum)

								if tmp:
									_gg_binary, asum = read_residue_prime95(f, asum)
						elif wu.state == ECM_STATE_STAGE2:
							(stage2_type,), asum = read_value_prime95(f, "<i", asum)

							if stage2_type != ECM_STAGE2_POLYMULT:
								(
									(
										_stage2_numvals,
										totrels,
										wu.D,
										_E,
										_TWO_FFT_STAGE2,
										_pool_type,
										_first_relocatable,
										_last_relocatable,
										wu.B2_start,
										_C_done,
										numDsections,
										Dsection,
										_max_pairmap_Dsections,
										_relp,
									),
									asum,
								) = read_value_prime95(f, "<QIIIiiQQQQQQQi", asum)

								_relp_sets, asum = read_array_prime95(f, 32 * 2, asum)

								(pairmap_size,), asum = read_value_prime95(f, "<Q", asum)

								_pairmap, asum = read_array_prime95(f, pairmap_size, asum)

								if options.check:
									_Qx_binary, asum = read_residue_prime95(f, asum)

									_gg_binary, asum = read_residue_prime95(f, asum)
							else:
								(_required_missing, _C_done), asum = read_value_prime95(f, "<iQ", asum)

								if options.check:
									_Qx_binary, asum = read_residue_prime95(f, asum)

									(tmp,), asum = read_value_prime95(f, "<i", asum)

									if tmp:
										_gg_binary, asum = read_residue_prime95(f, asum)
						elif wu.state == ECM_STATE_GCD:
							if options.check:
								_gg, asum = read_residue_prime95(f, asum)
			elif magicnum == PM1_MAGICNUM:
				if not 1 <= wu.version <= PM1_VERSION:
					logging.error("P-1 savefile with unsupported version = %s", wu.version)
					return None

				wu.work_type = WORK_PMINUS1

				if wu.version < 4:  # Version 25 through 30.3 save file
					(state,), asum = read_value_prime95(f, "<I", asum)

					if wu.version == 2:
						_max_stage0_prime = 13333333
					else:
						(_max_stage0_prime,), asum = read_value_prime95(f, "<I", asum)

					(
						(
							wu.B_done,
							wu.interim_B,
							wu.C_done,
							_C_start,
							wu.interim_C,
							processed,
							wu.D,
							wu.E,
							_rels_done,
							bitarray_len,
						),
						asum,
					) = read_value_prime95(f, "<QQQQQQIIII", asum)
					if bitarray_len:
						_bitarray, asum = read_array_prime95(f, bitarray_len, asum)

					(_bitarray_first_number, _pairs_set, _pairs_done), asum = read_value_prime95(f, "<QII", asum)

					if state == 3:
						wu.state = PM1_STATE_STAGE0
						wu.stage0_bitnum = processed
					elif state == 0:
						wu.state = PM1_STATE_STAGE1
						wu.stage1_prime = processed
					elif state == 1:
						wu.state = PM1_STATE_STAGE2
					elif state == 2:
						wu.state = PM1_STATE_DONE

					if options.check:
						_x, asum = read_residue_prime95(f, asum)

						if state == 1:
							_gg, asum = read_residue_prime95(f, asum)
				else:  # 4 <= version <= 7  # 30.4 to 30.7
					(wu.state,), asum = read_value_prime95(f, "<i", asum)

					if wu.state == PM1_STATE_STAGE0:
						(wu.interim_B, _max_stage0_prime, wu.stage0_bitnum), asum = read_value_prime95(
							f, "<Q" + ("II" if wu.version <= 5 else "QQ"), asum
						)
					elif wu.state == PM1_STATE_STAGE1:
						(wu.B_done, wu.interim_B, wu.stage1_prime), asum = read_value_prime95(f, "<QQQ", asum)
					elif wu.state == PM1_STATE_MIDSTAGE:
						(wu.B_done, wu.C_done), asum = read_value_prime95(f, "<QQ", asum)
					elif wu.state == PM1_STATE_STAGE2:
						if wu.version <= 6:
							(wu.B_done, wu.C_done, wu.interim_C, _stage2_numvals, _totrels, wu.D), asum = read_value_prime95(
								f, "<QQQIII", asum
							)

							if wu.version == 4:
								(wu.E,), asum = read_value_prime95(f, "<I", asum)

							(_first_relocatable, _last_relocatable, wu.B2_start, _numDsections, _Dsection), asum = (
								read_value_prime95(f, "<QQQQQ", asum)
							)

							if wu.version == 4:
								(bitarraymaxDsections, bitarrayfirstDsection), asum = read_value_prime95(f, "<QQ", asum)

								bitarray_numDsections = min(numDsections - bitarrayfirstDsection, bitarraymaxDsections)
								bitarray_len = -((bitarray_numDsections * totrels) // -8)
								bitarray_start = ((Dsection - bitarrayfirstDsection) * totrels) // 8
								_bitarray, asum = read_array_prime95(f, bitarray_len - bitarray_start, asum)
							else:
								(_max_pairmap_Dsections, _relp), asum = read_value_prime95(f, "<QI", asum)

								_relp_sets, asum = read_array_prime95(f, 32 * 2, asum)

								(pairmap_size,), asum = read_value_prime95(f, "<Q", asum)

								_pairmap, asum = read_array_prime95(f, pairmap_size, asum)
						else:
							(
								(
									wu.B_done,
									wu.C_done,
									wu.interim_C,
									stage2_type,
									wu.D,
									_numrels,
									wu.B2_start,
									_numDsections,
									_Dsection,
									_first_relocatable,
									_last_relocatable,
								),
								asum,
							) = read_value_prime95(f, "<QQQiiiQQQQQ", asum)

							if stage2_type == PM1_STAGE2_PAIRING:
								(_stage2_numvals, _totrels, _max_pairmap_Dsections, _relp), asum = read_value_prime95(
									f, "<iiQi", asum
								)

								_relp_sets, asum = read_array_prime95(f, 32 * 2, asum)

								(pairmap_size,), asum = read_value_prime95(f, "<Q", asum)

								_pairmap, asum = read_array_prime95(f, pairmap_size, asum)
							else:
								if wu.version > 7:
									(_required_missing,), asum = read_value_prime95(f, "<i", asum)
					elif wu.state == PM1_STATE_GCD:
						(wu.B_done, wu.C_done), asum = read_value_prime95(f, "<QQ", asum)
					elif wu.state == PM1_STATE_DONE:
						(wu.B_done, wu.C_done), asum = read_value_prime95(f, "<QQ", asum)

					if options.check:
						if wu.version == 4:
							have_x = True
						else:
							(have_x,), asum = read_value_prime95(f, "<i", asum)
						if have_x:
							_x, asum = read_residue_prime95(f, asum)

						if wu.version >= 5 and PM1_STATE_MIDSTAGE <= wu.state <= PM1_STATE_STAGE2:
							_invx, asum = read_residue_prime95(f, asum)

						if PM1_STATE_MIDSTAGE <= wu.state <= PM1_STATE_GCD:
							if wu.version == 4:
								have_gg = True
							else:
								(have_gg,), asum = read_value_prime95(f, "<i", asum)
							if have_gg:
								_gg, asum = read_residue_prime95(f, asum)
			elif magicnum == PP1_MAGICNUM:
				if not 1 <= wu.version <= PP1_VERSION:
					logging.error("P+1 savefile with unsupported version = %s", wu.version)
					return None

				wu.work_type = WORK_PPLUS1

				(wu.state, wu.numerator, wu.denominator), asum = read_value_prime95(f, "<iii", asum)

				if wu.state == PP1_STATE_STAGE1:
					(wu.B_done, wu.interim_B, wu.stage1_prime), asum = read_value_prime95(f, "<QQQ", asum)
				elif wu.state == PP1_STATE_MIDSTAGE:
					(wu.B_done, wu.C_done), asum = read_value_prime95(f, "<QQ", asum)
				elif wu.state == PP1_STATE_STAGE2:
					(
						(
							wu.B_done,
							wu.C_done,
							wu.interim_C,
							_stage2_numvals,
							totrels,
							_D,
							_first_relocatable,
							_last_relocatable,
							wu.B2_start,
							numDsections,
							Dsection,
						),
						asum,
					) = read_value_prime95(f, "<QQQiiiQQQQQ", asum)
					if wu.version == 1:
						(bitarraymaxDsections, bitarrayfirstDsection), asum = read_value_prime95(f, "<QQ", asum)

						bitarray_numDsections = min(numDsections - bitarrayfirstDsection, bitarraymaxDsections)
						bitarray_len = -((bitarray_numDsections * totrels) // -8)
						bitarray_start = ((Dsection - bitarrayfirstDsection) * totrels) // 8
						_bitarray, asum = read_array_prime95(f, bitarray_len - bitarray_start, asum)
					else:
						(_max_pairmap_Dsections, _relp), asum = read_value_prime95(f, "<Qi", asum)

						_relp_sets, asum = read_array_prime95(f, 32 * 2, asum)

						(pairmap_size,), asum = read_value_prime95(f, "<Q", asum)

						_pairmap, asum = read_array_prime95(f, pairmap_size, asum)
				elif wu.state == PP1_STATE_GCD:
					(wu.B_done, wu.C_done), asum = read_value_prime95(f, "<QQ", asum)
				elif wu.state == PP1_STATE_DONE:
					(wu.B_done, wu.C_done), asum = read_value_prime95(f, "<QQ", asum)

				if options.check:
					_V, asum = read_residue_prime95(f, asum)

					if PP1_STATE_MIDSTAGE <= wu.state <= PP1_STATE_GCD:
						if wu.version == 4:  # Prime95/MPrime bug
							have_gg = True
						else:
							(have_gg,), asum = read_value_prime95(f, "<i", asum)
						if have_gg:
							_gg, asum = read_residue_prime95(f, asum)
			else:
				logging.error("savefile with unknown magicnum = %#x", magicnum)
				return None

			if options.check and f.read():
				return None

			asum &= 0xFFFFFFFF

			if options.check and filesum != asum:
				logging.error("Checksum error. Got %X, expected %X.", filesum, asum)
	except EOFError:
		return None
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	return wu


def read_residue_mlucas(file, nbytes, filename, check=False):
	"""Reads and verifies the residue from an Mlucas work unit file."""
	residue = None
	if options.check or check:
		buffer = file.read(nbytes)
		if len(buffer) != nbytes:
			raise EOFError
		residue = from_bytes(buffer)
	else:
		file.seek(nbytes, 1)  # os.SEEK_CUR

	res64, res35m1, res36m1 = unpack("<Q5s5s", file)
	res35m1 = from_bytes(res35m1)
	res36m1 = from_bytes(res36m1)
	# print("{0:016X}".format(res64), "{0:010X}".format(res35m1), "{0:010X}".format(res36m1))
	if options.check:
		ares64 = residue & 0xFFFFFFFFFFFFFFFF
		if res64 != ares64:
			logging.error("%r: Res64 checksum error. Expected %X, got %X.", filename, res64, ares64)
		ares35m1 = residue % 0x7FFFFFFFF
		if res35m1 != ares35m1:
			logging.error("%r: Res35m1 checksum error. Expected %s, got %s.", filename, res35m1, ares35m1)
		ares36m1 = residue % 0xFFFFFFFFF
		if res36m1 != ares36m1:
			logging.error("%r: Res36m1 checksum error. Expected %s, got %s.", filename, res36m1, ares36m1)
		# print("{0:016X}".format(ares64), "{0:010X}".format(ares35m1), "{0:010X}".format(ares36m1))
	return residue, res64, res35m1, res36m1


def parse_work_unit_mlucas(filename, exponent, stage):
	"""Parses a Mlucas work unit file, extracting important information."""
	wu = work_unit()

	try:
		with open(filename, "rb") as f:
			t, m, tmp = unpack("<BB8s", f)
			nsquares = from_bytes(tmp)

			p = 1 << exponent if m == MODULUS_TYPE_FERMAT else exponent

			nbytes = (p + 7) // 8 if m == MODULUS_TYPE_MERSENNE else (p >> 3) + 1 if m == MODULUS_TYPE_FERMAT else 0

			residue1, res64, res35m1, res36m1 = read_residue_mlucas(
				f, nbytes, filename, options.jacobi and t == TEST_TYPE_PRIMALITY and m == MODULUS_TYPE_MERSENNE
			)

			result = unpack("<3sQ", f, True)
			kblocks = res_shift = None
			if result is not None:
				kblocks, res_shift = result
				kblocks = from_bytes(kblocks)

			if t == TEST_TYPE_PRP or (t == TEST_TYPE_PRIMALITY and m == MODULUS_TYPE_FERMAT):
				(prp_base,) = unpack("<I", f)

				_residue2, _i1, _i2, _i3 = read_residue_mlucas(f, nbytes, filename)

				(_gcheck_shift,) = unpack("<Q", f)

			result = unpack("<II", f, True)
			nerr_roe = nerr_gcheck = None
			if result is not None:
				nerr_roe, nerr_gcheck = result

			if t == TEST_TYPE_PRIMALITY:
				if m == MODULUS_TYPE_MERSENNE:
					wu.work_type = WORK_TEST

					wu.counter = nsquares

					wu.stage = "LL"
					wu.pct_complete = nsquares / (p - 2)

					if options.jacobi:
						if executor:
							executor.submit(jacobi_test, wu, p, residue1, filename)
						else:
							jacobi_test(wu, p, residue1, filename)
				elif m == MODULUS_TYPE_FERMAT:
					wu.work_type = WORK_PRP  # No Pépin worktype

					wu.counter = nsquares

					wu.stage = "Pépin"
					wu.pct_complete = nsquares / (p - 1)

				if options.check or (options.jacobi and m == MODULUS_TYPE_MERSENNE):
					wu.res2048 = "{0:0512X}".format(residue1 & (1 << 2048) - 1)
			elif t == TEST_TYPE_PRP:
				wu.work_type = WORK_PRP

				wu.counter = nsquares
				wu.prp_base = prp_base

				# if options.check and nsquares == p:
				#     a2 = prp_base * prp_base
				#     r = residue1 % a2
				#     if r:
				#         residue1 += (a2 - r * pow(p % a2, -1, a2) % a2) * p
				#     residue1 //= a2
				#     wu.isProbablePrime = residue1 == 1
				#     logging.debug("%s: Probable Prime: %s", filename, wu.isProbablePrime)

				wu.stage = "PRP"
				wu.pct_complete = nsquares / p

				if options.check:
					wu.res2048 = "{0:0512X}".format(residue1 & (1 << 2048) - 1)
			elif t == TEST_TYPE_PM1:
				wu.work_type = WORK_PMINUS1

				if stage == 1:
					wu.state = PM1_STATE_STAGE1
					wu.counter = nsquares
				elif stage == 2:
					wu.state = PM1_STATE_STAGE2
					wu.interim_C = from_bytes(tmp[:-1])
					_psmall = from_bytes(tmp[-1:])

				wu.stage = "S{0}".format(stage)
				wu.pct_complete = None  # ?
			else:
				logging.error("savefile with unknown TEST_TYPE = %s", t)
				return None

			if m == MODULUS_TYPE_MERSENNE:
				wu.n = p
			elif m == MODULUS_TYPE_FERMAT:
				wu.n = p
				wu.c = 1
			else:
				logging.error("savefile with unknown MODULUS_TYPE = %s", m)
				return None

			wu.res64 = "{0:016X}".format(res64)
			wu.res35m1 = res35m1
			wu.res36m1 = res36m1
			if kblocks is not None:
				wu.fftlen = kblocks << 10
			wu.shift_count = res_shift
			wu.nerr_roe = nerr_roe
			wu.nerr_gcheck = nerr_gcheck

			if options.check and f.read():
				return None
	except EOFError:
		return None
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	return wu


def parse_work_unit_cudalucas(filename, p):
	"""Parses a CUDALucas work unit file, extracting important information."""
	wu = work_unit(WORK_TEST)
	end = (p + 31) // 32

	try:
		with open(filename, "rb") as f:
			if options.check or options.jacobi:
				size = (end + 9) * 4
				buffer = f.read(size)
				if len(buffer) != size:
					return None
				if options.check:
					chksum = checkpoint_checksum(buffer)
				residue = from_bytes(buffer[: -9 * 4])

			f.seek(end * 4)

			q, n, j, offset, total_time, _time_adj, _iter_adj, _, magic_number, checksum = unpack("=IIIIIIIIII", f)
			if p != q:
				logging.error("Expecting the exponent %s, but found %s", p, q)
				return None
			if magic_number:
				logging.error("savefile with unknown magic_number = %s", magic_number)
			if options.check and checksum != chksum:
				logging.error("Checksum error. Got %X, expected %X.", checksum, chksum)
			total_time <<= 15
			_time_adj <<= 15

			wu.n = q
			wu.counter = j
			wu.shift_count = offset
			wu.fftlen = n
			wu.total_time = total_time

			wu.stage = "LL"
			wu.pct_complete = j / (q - 2)

			if options.check or options.jacobi:
				residue = rotr(residue, offset, q, (1 << q) - 1)
				wu.res64 = "{0:016X}".format(residue & 0xFFFFFFFFFFFFFFFF)
				wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)
			if options.jacobi:
				if executor:
					executor.submit(jacobi_test, wu, q, residue, filename)
				else:
					jacobi_test(wu, q, residue, filename)

			if options.check and f.read():
				return None
	except EOFError:
		return None
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	return wu


def parse_work_unit_cudapm1(filename, p):
	"""Parses a CUDAPm1 work unit file, extracting important information."""
	wu = work_unit(WORK_PMINUS1)
	end = (p + 31) // 32

	try:
		with open(filename, "rb") as f:
			f.seek(end * 4)

			(
				q,
				n,
				j,
				stage,
				time,
				b1,
				_,
				_,
				_,
				_,
				b2,
				d,
				e,
				_nrp,
				_m,
				_k,
				_t,
				itran_done1,
				itran_done2,
				ptran_done,
				itime,
				ptime,
				_,
				_,
				_,
			) = unpack("=IIIIIIIIIIIIIIIIIIIIIIIII", f)
			if p != q:
				logging.error("Expecting the exponent %s, but found %s", p, q)
				return None

			wu.pct_complete = None  # ?

			if not b2:
				wu.state = PM1_STATE_STAGE1
				wu.counter = j
				wu.total_time = time * 1000 * 1000
				wu.stage = "S1"
				if stage == 2:
					wu.pct_complete = 1.0
			else:
				wu.state = PM1_STATE_STAGE2
				wu.counter = itran_done1 + itran_done2 + ptran_done
				wu.C_done = b2
				wu.E = e
				wu.D = d
				wu.total_time = (itime + ptime) * 1000 * 1000
				wu.stage = "S2"

			wu.n = q
			wu.fftlen = n
			wu.B_done = b1

			if options.check and f.read():
				return None
	except EOFError:
		return None
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	return wu


def parse_work_unit_gpuowl(filename):
	"""Parses a GpuOwl work unit file, extracting important information."""
	wu = work_unit()

	try:
		with open(filename, "rb") as f:
			header = f.readline().rstrip(b"\n")

			if not header.startswith(b"OWL "):
				return None

			crc = None

			if header.startswith(b"OWL LL "):
				ll_v1 = LL_v1_RE.match(header)
				ll_v1a = LL_v1a_RE.match(header)

				wu.work_type = WORK_TEST
				ahash = None

				if ll_v1a:
					version, exponent, iteration, crc = ll_v1a.groups()
				elif ll_v1:
					version, exponent, iteration, ahash = ll_v1.groups()
				else:
					logging.error("LL savefile with unknown version: %s", header)
					return None

				wu.n = int(exponent)
				wu.counter = int(iteration)
				wu.shift_count = 0

				if options.check or options.jacobi:
					nWords = (wu.n - 1) // 32 + 1
					size = nWords * 4
					buffer = f.read(size)
					if len(buffer) != size:
						return None
					residue = from_bytes(buffer)
					wu.res64 = "{0:016X}".format(residue & 0xFFFFFFFFFFFFFFFF)
					wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)

				wu.stage = "LL"
				wu.pct_complete = wu.counter / (wu.n - 2)

				# Python 3.5+
				if options.check and hasattr(hashlib, "blake2b") and ahash is not None:
					ahash = int(ahash, 16)
					h = hashlib.blake2b(digest_size=8)
					h.update(struct.pack("=II", wu.n, wu.counter))
					h.update(buffer)
					aahash = from_bytes(h.digest())
					if ahash != aahash:
						logging.error("Hash error. Expected %X, actual %X.", ahash, aahash)
				if options.jacobi:
					if executor:
						executor.submit(jacobi_test, wu, wu.n, residue, filename)
					else:
						jacobi_test(wu, wu.n, residue, filename)
			elif header.startswith(b"OWL PRP "):
				prp_v9 = PRP_v9_RE.match(header)
				prp_v10 = PRP_v10_RE.match(header)
				prp_v11 = PRP_v11_RE.match(header)
				prp_v12 = PRP_v12_RE.match(header)

				wu.work_type = WORK_PRP
				nErrors = None

				if prp_v12:
					version, exponent, iteration, block_size, res64, nErrors, crc = prp_v12.groups()
				elif prp_v11:
					version, exponent, iteration, block_size, res64, nErrors, _B1, _nBits, _start, _nextK, crc = prp_v11.groups()
				elif prp_v10:
					version, exponent, iteration, block_size, res64, nErrors = prp_v10.groups()
				elif prp_v9:
					version, exponent, iteration, block_size, res64 = prp_v9.groups()
				else:
					logging.error("PRP savefile with unknown version: %s", header)
					return None

				wu.n = int(exponent)
				wu.counter = int(iteration)
				wu.shift_count = 0
				wu.L = int(block_size)
				wu.res64 = res64.decode().upper()
				if nErrors is not None:
					wu.nerr_gcheck = int(nErrors)

				if options.check:
					nWords = (wu.n - 1) // 32 + 1
					size = nWords * 4
					buffer = f.read(size)
					if len(buffer) != size:
						return None
					residue = from_bytes(buffer)
					# Getting the original residue from the GEC residue is currently too computationally expensive in Python
					# res64 = int(res64, 16)
					# ares64 = residue & 0xFFFFFFFFFFFFFFFF
					# if res64 != ares64:
					# logging.error("Res64 error. Expected %X, actual %X.", res64, ares64)
					wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)

				wu.stage = "PRP"
				wu.pct_complete = wu.counter / wu.n
			elif header.startswith((b"OWL PM1 ", b"OWL P1 ", b"OWL P1F ")):
				p1_v1 = P1_v1_RE.match(header)
				p1_v2 = P1_v2_RE.match(header)
				p1_v3 = P1_v3_RE.match(header)
				p1final_v1 = P1Final_v1_RE.match(header)

				wu.work_type = WORK_PMINUS1
				wu.pct_complete = None  # ?

				if p1_v3:
					version, exponent, B1, iteration, _block = p1_v3.groups()
					wu.counter = int(iteration)

					(crc,) = unpack("=I", f)
				elif p1_v2:
					version, exponent, B1, iteration, _nextK, crc = p1_v2.groups()
					wu.counter = int(iteration)
				elif p1_v1:
					version, exponent, B1, iteration, nBits = p1_v1.groups()
					wu.counter = int(iteration)
					wu.pct_complete = wu.counter / int(nBits)
				elif p1final_v1:
					version, exponent, B1, crc = p1final_v1.groups()
					wu.pct_complete = 1.0
				else:
					logging.error("P-1 stage 1 savefile with unknown version: %s", header)
					return None

				wu.state = PM1_STATE_STAGE1
				wu.n = int(exponent)
				wu.B_done = int(B1)

				if options.check:
					nWords = (wu.n - 1) // 32 + 1
					size = nWords * 4
					buffer = f.read(size)
					if len(buffer) != size:
						return None

				wu.stage = "S1"
			elif header.startswith(b"OWL P2 "):
				p2_v1 = P2_v1_RE.match(header)
				p2_v2 = P2_v2_RE.match(header)
				p2_v3 = P2_v3_RE.match(header)

				wu.work_type = WORK_PMINUS1
				wu.pct_complete = None  # ?
				nWords = None

				if p2_v3:
					version, exponent, B1, B2, D, _nBuf, nextBlock = p2_v3.groups()
					wu.D = int(D)
					if int(nextBlock) == 0xFFFFFFFF:  # (1 << 32) - 1
						wu.pct_complete = 1.0
				elif p2_v2:
					version, exponent, B1, B2, crc = p2_v2.groups()
				elif p2_v1:
					version, exponent, B1, B2, nWords, kDone = p2_v1.groups()
					nWords = int(nWords)
					wu.pct_complete = int(kDone) / 2880
				else:
					logging.error("P-1 stage 2 savefile with unknown version: %s", header)
					return None

				wu.state = PM1_STATE_STAGE2
				wu.n = int(exponent)
				wu.B_done = int(B1)
				wu.C_done = int(B2)

				if options.check and crc is not None:
					if nWords is None:
						nWords = (wu.n - 1) // 32 + 1
					size = nWords * 4
					buffer = f.read(size)
					if len(buffer) != size:
						return None

				wu.stage = "S2"
			elif header.startswith(b"OWL TF "):
				tf_v2 = TF_v2_RE.match(header)

				wu.work_type = WORK_FACTOR

				if tf_v2:
					version, exponent, bitLo, bitHi, classDone, classTotal = tf_v2.groups()
				else:
					logging.error("TF savefile with unknown version: %s", header)
					return None

				wu.n = int(exponent)
				wu.bits = int(bitLo)
				wu.test_bits = int(bitHi)

				wu.stage = "TF{0}".format(wu.bits)
				wu.pct_complete = int(classDone) / int(classTotal)
			else:
				logging.error("Unknown save/checkpoint file header: %s", header)
				return None

			# if options.check and f.read():
			# 	return None
	except EOFError:
		return None
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	if options.check and crc is not None:
		crc = int(crc)
		acrc = binascii.crc32(buffer) & 0xFFFFFFFF
		if crc != acrc:
			logging.error("CRC error. Expected %X, actual %X.", crc, acrc)

	wu.version = int(version)
	return wu


def parse_work_unit_prpll(filename):
	"""Parses a PRPLL work unit file, extracting important information."""
	wu = work_unit()

	try:
		with open(filename, "rb") as f:
			header = f.readline().rstrip(b"\n")

			if not header.startswith(b"OWL "):
				return None

			crc = None

			if header.startswith(b"OWL LL "):
				ll_v13 = LL_v13_RE.match(header)

				wu.work_type = WORK_TEST

				if ll_v13:
					version, exponent, iteration, elapsed = ll_v13.groups()

					(crc,) = unpack("=I", f)
				else:
					logging.error("LL savefile with unknown version: %s", header)
					return None

				wu.n = int(exponent)
				wu.counter = int(iteration)
				wu.shift_count = 0
				wu.total_time = int(float(elapsed) * 1000 * 1000)

				if options.check or options.jacobi:
					nWords = (wu.n - 1) // 32 + 1
					size = nWords * 4
					buffer = f.read(size)
					if len(buffer) != size:
						return None
					residue = from_bytes(buffer)
					wu.res64 = "{0:016X}".format(residue & 0xFFFFFFFFFFFFFFFF)
					wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)

				wu.stage = "LL"
				wu.pct_complete = wu.counter / (wu.n - 2)

				if options.jacobi:
					if executor:
						executor.submit(jacobi_test, wu, wu.n, residue, filename)
					else:
						jacobi_test(wu, wu.n, residue, filename)
			elif header.startswith(b"OWL PRP "):
				prp_v13 = PRP_v13_RE.match(header)

				wu.work_type = WORK_PRP

				if prp_v13:
					version, exponent, iteration, block_size, res64, nErrors, elapsed = prp_v13.groups()

					(crc,) = unpack("=I", f)
				else:
					logging.error("PRP savefile with unknown version: %s", header)
					return None

				wu.n = int(exponent)
				wu.counter = int(iteration)
				wu.shift_count = 0
				wu.L = int(block_size)
				wu.res64 = res64.decode().upper()
				wu.nerr_gcheck = int(nErrors)
				wu.total_time = int(float(elapsed) * 1000 * 1000)

				if options.check:
					nWords = (wu.n - 1) // 32 + 1
					size = nWords * 4
					buffer = f.read(size)
					if len(buffer) != size:
						return None
					residue = from_bytes(buffer)
					# Getting the original residue from the GEC residue is currently too computationally expensive in Python
					# res64 = int(res64, 16)
					# ares64 = residue & 0xFFFFFFFFFFFFFFFF
					# if res64 != ares64:
					# logging.error("Res64 error. Expected %X, actual %X.", res64, ares64)
					wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)

				wu.stage = "PRP"
				wu.pct_complete = wu.counter / wu.n
			else:
				logging.error("Unknown save/checkpoint file header: %s", header)
				return None

			if options.check and f.read():
				return None
	except EOFError:
		return None
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	if options.check and crc is not None:
		crc = int(crc)
		acrc = binascii.crc32(buffer) & 0xFFFFFFFF
		if crc != acrc:
			logging.error("CRC error. Expected %X, actual %X.", crc, acrc)

	wu.version = int(version)
	return wu


def calculate_k(exp, bits):
	"""
	calculates biggest possible k in "2 * exp * k + 1 < 2^bits"

	Because Python is not limited to 64-bit integers like C,
	we simply use the "bits <= 64" block from the C code
	"""

	tmp_low = 1 << (bits - 1)
	tmp_low -= 1
	k = tmp_low // exp

	if k == 0:
		k = 1
	return k


def class_needed(exp, k_min, c, more_classes, wagstaff):
	"""
	checks whether the class c must be processed or can be ignored at all because
	all factor candidates within the class c are a multiple of 3, 5, 7 or 11 (11
	only if MORE_CLASSES is defined) or are 3 or 5 mod 8 (Mersenne) or are 5 or 7 mod 8 (Wagstaff)

	k_min *MUST* be aligned in that way that k_min is in class 0!
	"""

	if (
		(2 * (exp % 8) * ((k_min + c) % 8)) % 8 != (6 if wagstaff else 2)
		and ((2 * (exp % 8) * ((k_min + c) % 8)) % 8 != 4)
		and ((2 * (exp % 3) * ((k_min + c) % 3)) % 3 != 2)
		and ((2 * (exp % 5) * ((k_min + c) % 5)) % 5 != 4)
		and ((2 * (exp % 7) * ((k_min + c) % 7)) % 7 != 6)
	):
		if not more_classes or (2 * (exp % 11) * ((k_min + c) % 11)) % 11 != 10:
			return True

	return False


def pct_complete_mfakt(exp, bits, num_classes, cur_class, wagstaff=False):
	"""
	Calculate percentage completeness of an mfaktc/mfakto checkpoint file
	using the same logic used to display Pct in mfaktc/mfakto output

	The code below is adapted from C code in mfaktc version 0.21 by user nclvrps@github

	Keep the same function names, variable names, comments, and overall formatting
	in order to ease modification if future versions of mfaktc.c are released.

	Note that mfaktc 0.21 is:
	Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014, 2015  Oliver Weihe (o.weihe@t-online.de)
	and is licensed under GPL v3
	"""
	# Lines of code with comments below are taken from mfaktc.c

	cur_class += 1  # the checkpoint contains the last complete processed class!

	if num_classes in {4620, 420}:
		if num_classes == 4620:
			more_classes = True
			max_class_number = 960
		elif num_classes == 420:
			more_classes = False
			max_class_number = 96

		k_min = calculate_k(exp, bits)
		k_min -= k_min % num_classes  # k_min is now 0 mod num_classes

		class_counter = sum(1 for i in range(cur_class) if class_needed(exp, k_min, i, more_classes, wagstaff))

		return class_counter / max_class_number

	# This should never happen
	return cur_class / num_classes


def parse_work_unit_mfaktc(filename):
	"""Parses a mfaktc work unit file, extracting important information."""
	wu = work_unit(WORK_FACTOR)

	try:
		with open(filename, "rb") as f:
			header = f.readline().rstrip(b"\n")

			if options.check and f.read():
				return None
	except (IOError, OSError):
		logging.exception("Error reading %R file.", filename)
		return None

	mfaktc_tf = MFAKTC_TF_RE.match(header)

	if mfaktc_tf:
		name_numbers, exp, bit_min, bit_max, num_classes, version, cur_class, num_factors, _factors_string, bit_level_time, i = (
			mfaktc_tf.groups()
		)
	else:
		return None

	if options.check:
		chksum = checkpoint_checksum(header.rsplit(None, 1)[0])
		i = int(i, 16)
		if chksum != i:
			logging.error("Checksum error. Got %X, expected %X.", chksum, i)

	wagstaff = name_numbers == b"W"  # Wagstaff
	if wagstaff:
		wu.c = 1
		wu.known_factors = (3,)

	wu.n = int(exp)
	wu.bits = int(bit_min)
	wu.test_bits = int(bit_max)
	wu.num_factors = int(num_factors)
	if bit_level_time:
		# wu.known_factors = [int(factor[1:-1]) for factor in factors_string.split(b",")]
		wu.total_time = int(bit_level_time) * 1000

	wu.stage = "TF{0}".format(wu.bits)
	wu.pct_complete = pct_complete_mfakt(wu.n, wu.bits, int(num_classes), int(cur_class), wagstaff)

	wu.version = version.decode()
	return wu


def parse_work_unit_mfakto(filename):
	"""Parses a mfakto work unit file, extracting important information."""
	wu = work_unit(WORK_FACTOR)

	try:
		with open(filename, "rb") as f:
			header = f.readline().rstrip(b"\n")

			if options.check and f.read():
				return None
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	mfakto_tf = MFAKTO_TF_RE.match(header)

	if mfakto_tf:
		exp, bit_min, bit_max, num_classes, version, cur_class, num_factors, _factors_string, bit_level_time, i = mfakto_tf.groups()
	else:
		return None

	if options.check:
		chksum = checkpoint_checksum(header.rsplit(None, 1)[0])
		i = int(i, 16)
		if chksum != i:
			logging.error("Checksum error. Got %X, expected %X.", chksum, i)

	wu.n = int(exp)
	wu.bits = int(bit_min)
	wu.test_bits = int(bit_max)
	wu.num_factors = int(num_factors)
	if bit_level_time:
		# wu.known_factors = [int(factor[1:-1]) for factor in factors_string.split(b",")]
		wu.total_time = int(bit_level_time) * 1000

	wu.stage = "TF{0}".format(wu.bits)
	wu.pct_complete = pct_complete_mfakt(wu.n, wu.bits, int(num_classes), int(cur_class))

	wu.version = version.decode()
	return wu


def parse_proof(filename):
	"""Parse a PRP proof file and return a work unit object with extracted data."""
	wu = work_unit(WORK_PRP)

	try:
		with open(filename, "rb") as f:
			header = f.readline().rstrip(b"\n")
			if header != b"PRP PROOF":
				return None

			header, _, version = f.readline().rstrip(b"\n").partition(b"=")
			if header != b"VERSION":
				logging.error("Error getting version number from proof header")
				return None
			wu.version = int(version)
			if wu.version not in {1, 2}:
				logging.error("PRP proof file with unknown version = %s", version)
				return None

			header, _, _hashlen = f.readline().rstrip(b"\n").partition(b"=")
			if header != b"HASHSIZE":
				logging.error("Error getting hash size from proof header")
				return None

			header, _, power = f.readline().rstrip(b"\n").partition(b"=")
			power, _, power_mult = power.partition(b"x")
			if header != b"POWER":
				logging.error("Error getting power from proof header")
				return None
			wu.proof_power = int(power)
			wu.proof_power_mult = int(power_mult) if power_mult else 1

			header = f.readline().rstrip(b"\n")
			if header.startswith(b"BASE="):
				_header, _, base = header.partition(b"=")
				wu.prp_base = int(base)
				header = f.readline().rstrip(b"\n")
			else:
				wu.prp_base = 3

			header, _, number = header.partition(b"=")
			if header != b"NUMBER":
				logging.error("Error getting number from proof header")
				return None
			proof_number = PROOF_NUMBER_RE.match(number)
			if not proof_number:
				logging.error("Error parsing number: %r", number)
				return None
			_, number, exponent, k, b, n, c, factors = proof_number.groups()
			if exponent:
				if number.startswith(b"M"):
					wu.n = int(exponent)
				elif number.startswith(b"F"):
					wu.n = 1 << int(exponent)
					wu.c = 1
				else:
					wu.c = int(exponent) - 1
			else:
				if k:
					wu.k = float(k)
				wu.b = int(b)
				wu.n = int(n)
				wu.c = int(c)
			if factors:
				wu.known_factors = tuple(map(int, factors.split(b"/")))

			proof_header_size = f.tell()
			f.seek(0, 2)  # os.SEEK_END
			proof_file_size = f.tell()
			residue_size = -(int(math.ceil(log2(wu.k) + wu.n * log2(wu.b))) // -8)
			proofs_written = (proof_file_size - proof_header_size) // ((wu.proof_power + 1) * residue_size)

			if options.check and wu.version == 2 and proofs_written == wu.proof_power_mult:
				f.seek(proof_header_size)
				for _ in range(1, wu.proof_power_mult):
					f.seek((wu.proof_power + 1) * residue_size, 1)  # os.SEEK_CUR
				buffer = f.read(residue_size)
				if len(buffer) != residue_size:
					return None
				residue = from_bytes(buffer)
				if wu.c != 1:
					modulus = int(wu.k) * (1 << wu.n) + wu.c
					# Python 3.8+
					# Much slower: pow(wu.prp_base, wu.c - 1, modulus)
					inverse = pow(pow(wu.prp_base, 1 - wu.c, modulus), -1, modulus)
					residue = (residue * inverse) % modulus
				wu.res64 = "{0:016X}".format(residue & 0xFFFFFFFFFFFFFFFF)
				wu.res2048 = "{0:0512X}".format(residue & (1 << 2048) - 1)
	except (IOError, OSError):
		logging.exception("Error reading %r file.", filename)
		return None

	wu.stage = "Proof"
	wu.pct_complete = proofs_written / wu.proof_power_mult
	return wu


def one_line_status(file, num, index, wu):
	"""Generates a one-line status summary for a given work unit."""
	stage = None
	if wu.work_type == WORK_CERT:
		work_type_str = "Certify"
		temp = ["Iter: {0:n}".format(wu.counter)]
		if wu.shift_count is not None:
			temp.append("Shift: {0:n}".format(wu.shift_count))
	elif wu.work_type == WORK_FACTOR:
		work_type_str = "Factor"
		temp = ["Bits: {0}{1}".format(wu.bits, " to {0}".format(wu.test_bits) if wu.test_bits else "")]
		if wu.factor_found:
			temp.append("Factor found!")
		if wu.num_factors:
			temp.append("{0:n} factor{1} found!".format(wu.num_factors, "s" if wu.num_factors > 1 else ""))
	elif wu.work_type == WORK_TEST:
		# work_type_str = "Lucas-Lehmer"
		work_type_str = "LL"
		# temp = ["Iter: {0:n} / {1:n}".format(wu.counter, wu.n - 2)]
		temp = ["Iter: {0:n}".format(wu.counter), "", ""]
		if wu.shift_count is not None:
			temp.append("Shift: {0:n}".format(wu.shift_count))
		if wu.fftlen:
			temp.append("FFT: {0}".format(outputunit(wu.fftlen, scale.IEC)))
		if options.jacobi:
			temp.append("Jacobi: {0:n} ({1})".format(wu.jacobi, "Passed" if wu.jacobi == -1 else "Failed"))
	elif wu.work_type == WORK_PRP:
		work_type_str = "PRP"
		# temp = ["Iter: {0:n} / {1:n}".format(wu.counter, wu.n)]
		temp = ["Iter: {0:n}".format(wu.counter) if wu.counter is not None else "", "", ""]
		if wu.shift_count is not None:
			temp.append("Shift: {0:n}".format(wu.shift_count))
		if wu.fftlen:
			temp.append("FFT: {0}".format(outputunit(wu.fftlen, scale.IEC)))
		if wu.L:
			temp.append("Block Size: {0:n}".format(wu.L))
		if wu.prp_base and wu.prp_base != 3:
			temp.append("Base: {0}".format(wu.prp_base))
		if wu.residue_type and wu.residue_type != 1:
			temp.append("Residue Type: {0}".format(wu.residue_type))
		if wu.proof_power:
			temp.append(
				"Proof Power: {0}{1}".format(wu.proof_power, "x{0}".format(wu.proof_power_mult) if wu.proof_power_mult > 1 else "")
			)
	elif wu.work_type == WORK_ECM:
		work_type_str = "ECM"
		stage = ECM_STATES[wu.state]
		temp = ["{0} Curve #{01:n}, s={2:.0f}".format(ECM_SIGMA_TYPES[wu.sigma_type], wu.curve, wu.sigma), "B1={0}".format(wu.B)]
		if wu.C:
			temp.append("B2={0}".format(wu.C))
		if wu.B2_start:
			temp.append("B2_start={0}".format(wu.B2_start))
	elif wu.work_type == WORK_PMINUS1:
		work_type_str = "P-1"
		stage = PM1_STATES[wu.state]
		B1 = wu.interim_B or wu.B_done or wu.stage0_bitnum
		B2 = wu.interim_C or wu.C_done
		# if B2 and B2 > B1:
		temp = [
			"E={0}{1}".format(wu.E, ", Iter: {0:n}".format(wu.counter) if wu.counter else "")
			if wu.E is not None and wu.E >= 2
			else "Iter: {0:n}".format(wu.counter)
			if wu.counter
			else "",
			"B1={0}".format(B1) if B1 else "",
			"B2={0}".format(B2) if B2 else "",
		]
		if wu.B2_start:
			temp.append("B2_start={0}".format(wu.B2_start))
		if wu.shift_count is not None:
			temp.append("Shift: {0:n}".format(wu.shift_count))
		if wu.fftlen:
			temp.append("FFT: {0}".format(outputunit(wu.fftlen, scale.IEC)))
	elif wu.work_type == WORK_PPLUS1:
		work_type_str = "P+1"
		stage = PP1_STATES[wu.state]
		B1 = wu.interim_B or wu.B_done
		temp = ["Start={0}/{1}".format(wu.numerator, wu.denominator), "B1={0}".format(B1)]
		B2 = wu.interim_C or wu.C_done
		# if B2 and B2 > B1:
		if B2:
			temp.append("B2={0}".format(B2))
		if wu.B2_start:
			temp.append("B2_start={0}".format(wu.B2_start))

	if wu.res64:
		if options.long and (wu.res35m1 is not None or wu.res36m1 is not None):
			temp.extend((
				"Res64: {0}".format(wu.res64),
				"Res35m1: {0}".format(wu.res35m1) if wu.res35m1 is not None else "",
				"Res36m1: {0}".format(wu.res36m1) if wu.res36m1 is not None else "",
			))
		else:
			temp.append("Residue: {0}".format(wu.res64))
	if wu.total_time:
		temp.append(
			"Time: {0}{1}".format(
				timedelta(microseconds=wu.total_time),
				", {0:n} ms/iter".format((wu.total_time / wu.counter) / 1000) if wu.counter else "",
			)
		)
	if wu.error_count:
		error_count = wu.error_count
		temp.append(
			"Errors: {0:08X}{1}{2}{3}".format(
				error_count,
				", Roundoff: {0:n}".format((error_count >> 8) & 0x3F) if error_count & 0x3F00 else "",
				", Jacobi: {0:n}".format((error_count >> 4) & 0xF) if error_count & 0xF0 else "",
				", Gerbicz: {0:n}".format((error_count >> 20) & 0xF) if error_count & 0xF00000 else "",
			)
		)
	if wu.nerr_roe:
		temp.append("Roundoff errors: {0:n}".format(wu.nerr_roe))
	if wu.nerr_gcheck:
		temp.append("Gerbicz errors: {0:n}".format(wu.nerr_gcheck))

	result = [
		assignment_to_str(wu) if not index else "",
		"{0:n}. {1}".format(num + 1, os.path.basename(file)) if num >= 0 else os.path.basename(file),
	]
	if options.long:
		mtime = os.path.getmtime(file)
		date = datetime.fromtimestamp(mtime)
		size = os.path.getsize(file)
		result += ("{0}B".format(outputunit(size)), "{0:%c}".format(date))
	result += [
		work_type_str,
		"{0}, {1}".format(stage, wu.stage) if stage else "Stage: {0}".format(wu.stage),
		"?%" if wu.pct_complete is None else "{0:.4%}".format(wu.pct_complete),
	] + temp

	return result


def json_status(file, wu, program):
	"""Generate a JSON-compatible status dictionary for a given work unit and program."""
	result = OrderedDict((
		("program", program),
		("k", wu.k),
		("b", wu.b),
		("n", wu.n),
		("c", wu.c),
		("exponent", assignment_to_str(wu)),
		("work_type", wu.work_type),
		("stage", wu.stage),
		("pct_complete", wu.pct_complete),
		("version", wu.version),
	))
	if wu.known_factors is not None:
		result["known_factors"] = tuple(map(str, wu.known_factors))
	if options.long:
		result["date"] = os.path.getmtime(file)
		result["size"] = os.path.getsize(file)

	if wu.work_type == WORK_CERT:
		result["counter"] = wu.counter
		if wu.shift_count is not None:
			result["shift_count"] = wu.shift_count
	elif wu.work_type == WORK_FACTOR:
		result["bits"] = wu.bits
		if wu.test_bits:
			result["test_bits"] = wu.test_bits
		if wu.factor_found is not None:
			result["factor_found"] = wu.factor_found
		if wu.num_factors is not None:
			result["num_factors"] = wu.num_factors
	elif wu.work_type == WORK_TEST:
		result["counter"] = wu.counter
		if wu.shift_count is not None:
			result["shift_count"] = wu.shift_count
		if wu.fftlen:
			result["fftlen"] = wu.fftlen
		if options.jacobi:
			result["jacobi"] = wu.jacobi
	elif wu.work_type == WORK_PRP:
		if wu.counter is not None:
			result["counter"] = wu.counter
		if wu.shift_count is not None:
			result["shift_count"] = wu.shift_count
		if wu.fftlen:
			result["fftlen"] = wu.fftlen
		if wu.L:
			result["L"] = wu.L
		if wu.prp_base:
			result["prp_base"] = wu.prp_base
		if wu.residue_type:
			result["residue_type"] = wu.residue_type
		if wu.proof_power:
			result["proof_power"] = wu.proof_power
			result["proof_power_mult"] = wu.proof_power_mult
		if wu.isProbablePrime is not None:
			result["isProbablePrime"] = wu.isProbablePrime
	elif wu.work_type == WORK_ECM:
		result["state"] = wu.state
		result["curve"] = wu.curve
		result["sigma"] = wu.sigma
		result["sigma_type"] = wu.sigma_type
		result["B"] = wu.B
		if wu.C is not None:
			result["C"] = wu.C
		if wu.D is not None:
			result["D"] = wu.D
		if wu.B2_start is not None:
			result["B2_start"] = wu.B2_start
	elif wu.work_type == WORK_PMINUS1:
		result["state"] = wu.state
		if wu.E is not None:
			result["E"] = wu.E
		if wu.counter:
			result["counter"] = wu.counter
		if wu.interim_B is not None:
			result["interim_B"] = wu.interim_B
		if wu.B_done is not None:
			result["B_done"] = wu.B_done
		if wu.stage0_bitnum is not None:
			result["stage0_bitnum"] = wu.stage0_bitnum
		if wu.interim_C is not None:
			result["interim_C"] = wu.interim_C
		if wu.C_done is not None:
			result["C_done"] = wu.C_done
		if wu.D is not None:
			result["D"] = wu.D
		if wu.B2_start is not None:
			result["B2_start"] = wu.B2_start
		if wu.shift_count is not None:
			result["shift_count"] = wu.shift_count
		if wu.fftlen:
			result["fftlen"] = wu.fftlen
	elif wu.work_type == WORK_PPLUS1:
		result["state"] = wu.state
		result["numerator"] = wu.numerator
		result["denominator"] = wu.denominator
		if wu.interim_B is not None:
			result["interim_B"] = wu.interim_B
		if wu.B_done is not None:
			result["B_done"] = wu.B_done
		if wu.interim_C is not None:
			result["interim_C"] = wu.interim_C
		if wu.C_done is not None:
			result["C_done"] = wu.C_done
		if wu.B2_start is not None:
			result["B2_start"] = wu.B2_start

	if wu.res64:
		result["res64"] = wu.res64
	if wu.res35m1 is not None:
		result["res35m1"] = wu.res35m1
	if wu.res36m1 is not None:
		result["res36m1"] = wu.res36m1
	if wu.res2048:
		result["res2048"] = wu.res2048
	if wu.total_time:
		result["total_time"] = wu.total_time
	if wu.error_count is not None:
		result["error_count"] = wu.error_count
	if wu.nerr_roe is not None:
		result["nerr_roe"] = wu.nerr_roe
	if wu.nerr_gcheck is not None:
		result["nerr_gcheck"] = wu.nerr_gcheck

	return result


def main(dirs):
	"""The main function to execute the script, handling command-line arguments and processing."""
	results = OrderedDict()

	for adir in dirs:
		aresults = results[adir] = OrderedDict()
		if options.prime95:
			aaresults = aresults["Prime95/MPrime"] = []
			entries = OrderedDict()
			for entry in glob.iglob(os.path.join(adir, "[pfemnc][A-Y0-9]*")):
				filename = os.path.basename(entry)
				match = PRIME95_RE.match(filename)
				if match:
					root, _ = os.path.splitext(filename)
					entries.setdefault(root, []).append((
						int(match.group(2)) if match.group(2) else 1 if match.group(1) else 0,
						entry,
					))
			for entry in entries.values():
				for j, (num, file) in enumerate(sorted(entry)):
					result = parse_work_unit_prime95(file)
					if result is not None:
						aaresults.append((j, num, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.mlucas:
			aaresults = aresults["Mlucas"] = []
			entries = OrderedDict()
			for entry in glob.iglob(os.path.join(adir, "[pfq][0-9]*")):
				match = MLUCAS_RE.match(os.path.basename(entry))
				if match:
					exponent = int(match.group(2))
					stage = match.group(3) and int(match.group(3))
					entries.setdefault(exponent, []).append((
						1 if stage is None else stage,
						-1 if match.group(4) else 0 if stage or match.group(1) in {"p", "f"} else 1,
						entry,
					))
			for exponent, entry in entries.items():
				for j, (stage, num, file) in enumerate(sorted(entry)):
					result = parse_work_unit_mlucas(file, exponent, stage)
					if result is not None:
						aaresults.append((j, num, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.cudalucas:
			aaresults = aresults["CUDALucas"] = []
			entries = OrderedDict()
			for entry in glob.iglob(os.path.join(adir, "[ct][0-9]*")):
				match = CUDALUCAS_RE.match(os.path.basename(entry))
				if match:
					exponent = int(match.group(2))
					entries.setdefault(exponent, []).append((0 if match.group(1) == "c" else 1, entry))
			for exponent, entry in entries.items():
				for j, (num, file) in enumerate(sorted(entry)):
					result = parse_work_unit_cudalucas(file, exponent)
					if result is not None:
						aaresults.append((j, num, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.cudapm1:
			aaresults = aresults["CUDAPm1"] = []
			entries = OrderedDict()
			for entry in glob.iglob(os.path.join(adir, "[ct][0-9]*s[12]")):
				match = CUDAPM1_RE.match(os.path.basename(entry))
				if match:
					exponent = int(match.group(2))
					entries.setdefault(exponent, []).append((int(match.group(3)), 0 if match.group(1) == "c" else 1, entry))
			for exponent, entry in entries.items():
				for j, (_stage, num, file) in enumerate(sorted(entry)):
					result = parse_work_unit_cudapm1(file, exponent)
					if result is not None:
						aaresults.append((j, num, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.gpuowl:
			aaresults = aresults["GpuOwl"] = []
			entries = OrderedDict()
			for entry in (
				aglob
				for globs in (
					os.path.join(adir, "ll-[0-9]*", "[0-9]*.*"),
					os.path.join(adir, "[0-9]*", "[0-9]*.*"),
					os.path.join(adir, "[0-9]*", "unverified.*"),
					os.path.join(adir, "[0-9]*.owl"),
				)
				for aglob in glob.iglob(globs)
			):
				match = GPUOWL_RE.search(entry)
				if match:
					exponent = int(match.group(1))
					entries.setdefault(exponent, []).append((
						-1 if match.group(3) or match.group(4) else 1 if match.group(5) or match.group(6) or match.group(7) else 0,
						entry,
					))
			for entry in entries.values():
				for j, (num, file) in enumerate(sorted(entry)):
					result = parse_work_unit_gpuowl(file)
					if result is not None:
						aaresults.append((j, num, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.prpll:
			aaresults = aresults["PRPLL"] = []
			entries = OrderedDict()
			for entry in (
				aglob
				for globs in (
					os.path.join(adir, "ll-[0-9]*", "[0-9]*-[0-9]*.ll"),
					os.path.join(adir, "[0-9]*", "[0-9]*-[0-9]*.prp"),
					os.path.join(adir, "[0-9]*", "unverified.prp"),
				)
				for aglob in glob.iglob(globs)
			):
				match = PRPLL_RE.search(entry)
				if match:
					exponent = int(match.group(1))
					entries.setdefault(exponent, []).append((-1 if match.group(3) else 0, entry))
			for entry in entries.values():
				for j, (num, file) in enumerate(sorted(entry)):
					result = parse_work_unit_prpll(file)
					if result is not None:
						aaresults.append((j, num, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.mfaktc:
			aaresults = aresults["mfaktc"] = []
			for file in glob.iglob(os.path.join(adir, "[MW][0-9]*.ckp")):
				if MFAKTC_RE.match(os.path.basename(file)):
					result = parse_work_unit_mfaktc(file)
					if result is not None:
						aaresults.append((0, -1, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.mfakto:
			aaresults = aresults["mfakto"] = []
			entries = OrderedDict()
			for entry in glob.iglob(os.path.join(adir, "M[0-9]*.ckp*")):
				match = MFAKTO_RE.match(os.path.basename(entry))
				if match:
					exponent = match.group(1)
					entries.setdefault(exponent, []).append((1 if match.group(2) else 0, entry))
			for entry in entries.values():
				for j, (num, file) in enumerate(sorted(entry)):
					result = parse_work_unit_mfakto(file)
					if result is not None:
						aaresults.append((j, num, file, result))
					else:
						logging.error("unable to parse the %r save/checkpoint file", file)

		if options.proof:
			aaresults = aresults["PRP proof"] = []
			for file in (
				aglob
				for globs in (os.path.join(adir, "*.proof*"), os.path.join(adir, "proof", "*.proof*"))
				for aglob in glob.iglob(globs)
			):
				if file.endswith((".proof", ".proof.tmp")):
					result = parse_proof(file)
					if result is not None:
						aaresults.append((0, -1, file, result))
					else:
						logging.error("unable to parse the %r proof file", file)

	if executor:
		executor.shutdown()

	parsed = OrderedDict()

	for i, (adir, aresults) in enumerate(results.items()):
		if i:
			print()
		print("{0}:".format(adir))
		for program, aaresults in aresults.items():
			if len(aresults) > 1:
				print("\t{0}:".format(program))
			rows = []
			for j, num, file, result in aaresults:
				rows.append(one_line_status(file, num, j, result))
				if options.json:
					parsed[file] = json_status(file, result, program)
			if rows:
				output_table(rows)
			else:
				print("\tNo save/checkpoint files found for {0}.".format(program))

	if options.json:
		with open(options.json, "w") as f:
			json.dump(parsed, f, ensure_ascii=False, indent=4)


if __name__ == "__main__":
	parser = optparse.OptionParser(
		version="%prog 1.0",
		description="Read Prime95/MPrime, Mlucas, GpuOwl, PRPLL, CUDALucas, CUDAPm1, mfaktc and mfakto save/checkpoint and proof files",
	)
	parser.add_option("-w", "--workdir", default=os.curdir, help="Working directory, Default: %default (current directory)")
	# parser.add_option("-D", "--dir", action="append", dest="dirs", help="Directories with the save/checkpoint files. Provide once for each directory.")
	parser.add_option("-p", "--prime95", "--mprime", action="store_true", help="Look for Prime95/MPrime save/checkpoint files")
	parser.add_option("-m", "--mlucas", action="store_true", help="Look for Mlucas save/checkpoint files")
	parser.add_option("-g", "--gpuowl", action="store_true", help="Look for GpuOwl save/checkpoint files")
	parser.add_option("--prpll", action="store_true", help="Look for PRPLL save/checkpoint files")
	parser.add_option("-c", "--cudalucas", action="store_true", help="Look for CUDALucas save/checkpoint files")
	parser.add_option("--cudapm1", action="store_true", help="Look for CUDAPm1 save/checkpoint files")
	parser.add_option("--mfaktc", action="store_true", help="Look for mfaktc save/checkpoint files")
	parser.add_option("--mfakto", action="store_true", help="Look for mfakto save/checkpoint files")
	parser.add_option("--proof", action="store_true", help="Look for PRP proof files")
	parser.add_option("-l", "--long", action="store_true", help="Output in long format with the file size and modification time")
	parser.add_option(
		"--check",
		action="store_true",
		help="Verify any checksums, CRCs or residues in save/checkpoint files. Also, calculate the Res64 and Res2048 values from any LL/PRP/CERT savefiles or version 2 PRP proof files. This may be computationally expensive.",
	)
	parser.add_option(
		"--jacobi",
		action="store_true",
		help="Run the Jacobi Error Check on LL save/checkpoint files. This may be very computationally expensive.",
	)
	parser.add_option("--json", help="Export data as JSON to this file")

	options, args = parser.parse_args()
	# if args:
	# parser.error("Unexpected argument: {0!r}".format(args[0]))

	workdir = os.path.expanduser(options.workdir)
	dirs = [os.path.join(workdir, adir) for adir in args] if args else [workdir]

	for adir in dirs:
		if not os.path.isdir(adir):
			parser.error("Directory {0!r} does not exist".format(adir))

	if not (
		options.prime95
		or options.mlucas
		or options.cudalucas
		or options.cudapm1
		or options.gpuowl
		or options.prpll
		or options.mfaktc
		or options.mfakto
		or options.proof
	):
		parser.error("Must select at least one GIMPS program to look for save/checkpoint files for")

	if options.json and os.path.exists(options.json):
		parser.error("File {0!r} already exists".format(options.json))

	logging.basicConfig(level=logging.DEBUG, format="%(filename)s: [%(asctime)s]  %(levelname)s: %(message)s")

	main(dirs)
