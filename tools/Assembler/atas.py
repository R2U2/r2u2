import sys
import os
import re

from .config import data
from .util import toBinary
from .filters import parse_filter, valid_filters

def assemble(f):
	binary = ""

	for line in f:
		if re.fullmatch('\s*', line):
			break

		max_at_width = int(data['L_ATOMIC_ADDR'])
		max_sig_width = int(data['L_SIG_ADDR'])
		max_const_width = int(data['L_NUM'])

		filters = valid_filters()

		instr = line.split()

		atomic = instr[0][1:-1]
		filt   = instr[1]
		cond   = instr[2]
		comp   = instr[3]
		args   = instr[4:]

		if atomic is None:
			print("ERROR: atomic not valid in instruction " + line)
			binary += "00000000"
		else:
			binary += toBinary(atomic, max_at_width)

		if filt in filters:
			binary += toBinary(filters.index(filt), data['L_FILTER'])
		else:
			print("ERROR: filter is not valid in instruction " + line)
			binary += toBinary(0, data['L_FILTER'])

		if cond == "==":
			binary += "000"
		elif cond == "!=":
			binary += "001"
		elif cond == "<":
			binary += "010"
		elif cond == "<=":
			binary += "011"
		elif cond == ">":
			binary += "100"
		elif cond == ">=":
			binary += "101"
		else:
			print("ERROR: comparison operator is not valid in instruction " + line)
			binary += "111"

		# Check if comparing to signal value or constant
		if comp[0] == "s":
			binary += "1"
			binary += toBinary(comp[1:], max_const_width)
			comp_width = int.bit_length(int(comp[1:]))
		else:
			binary += "0"
			binary += toBinary(comp, max_const_width)
			comp_width = int.bit_length(int(comp))

		if filt in filters:
			binary += parse_filter(filt,args)

		binary += "\\n"

		# Give warning if specs do not fit in desired configuration
		if int(atomic) > int(data['N_ATOMICS']):
			print('WARNING: Atomic index larger than maximum in line ' + line)
		if comp_width > max_const_width:
			print('NOTE: Constant value larger than maximum in line ' + line)
			print('Constant value will be truncated')

	return binary


prog_text = \
"""
#include "at_globals.h"
char *at_bin = "
""".strip()


def assemble_at(atasm, gen_dir, no_binaries):
	print('Assembling AT')
	f = open(atasm, 'r')
	bin_dir = gen_dir+'binary_files/'
	if(not os.path.isdir(bin_dir)):
		os.mkdir(bin_dir)
	binary = assemble(f)
	f.close()

	if no_binaries == 'True':
		global prog_text
		prog_text += binary + "\";\n"
		with open(gen_dir+'config.c', 'a') as c:
			c.write(prog_text)
	else:
		with open(bin_dir+'at.bin', 'w') as at:
			at.write(binary.replace('\\n','\n'))
