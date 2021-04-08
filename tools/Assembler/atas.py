import sys
import os
import re

from .config import data

def toBinary(value, width):
	value = int(value)

	# TODO: Enable AT compiler to handle floating point numbers

	# Handle sign
	if value < 0:
		# Convert to 2's complement
		value += 1
		b = bin(value)[3:]

		# Flip bits
		tmp = ''
		for digit in b:
			if digit == '0':
				tmp += '1'
			else:
				tmp += '0'
		b = tmp

		# Pad with 1s
		while len(b) < width:
			b = '1' + b
	else:
		b = bin(value)[2:]
		while len(b) < width:
			b = '0' + b

	return b

def assemble(f):
	binary = ""

	max_at_width = int.bit_length(int(data['N_ATOMICS']))
	max_sig_width = int.bit_length(int(data['N_SIGS']))
	max_const_width = int(data['L_NUM'])

	for line in f:
		if re.fullmatch('\s*', line):
			break

		instr = line.split()

		atomic = instr[0][1:-1]
		filter = instr[1]
		signal = instr[2][1:]
		arg    = instr[3]
		cond   = instr[4]
		comp   = instr[5]

		if atomic is None:
			print("Error: atomic not valid in instruction " + line)
			binary += "00000000"
		else:
			binary += toBinary(atomic, max_at_width)

		if filter == "bool":
			binary += "0001"
		elif filter == "int":
			binary += "0010"
		elif filter == "double":
			binary += "0011"
		elif filter == "rate":
			binary += "0100"
		elif filter == "abs_diff_angle":
			binary += "0101"
		elif filter == "movavg":
			binary += "0110"
		else:
			print("Error: filter is not valid in instruction " + line)
			binary += "0000"

		binary += toBinary(signal, max_sig_width)
		binary += toBinary(arg, max_const_width)

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
			print("Error: comparison operator is not valid in instruction " + line)
			binary += "111"

		# Check if comparing to signal value or constant
		if comp[0] == "s":
			binary += "1"
			binary += toBinary(comp[1:], max_const_width)
		else:
			binary += "0"
			binary += toBinary(comp, max_const_width)

		binary += "\\n"

		# Give warning if specs do not fit in desired configuration
		arg_width = int.bit_length(int(arg))
		comp_width = int.bit_length(int(comp))
		if int(atomic) > int(data['N_ATOMICS']):
			print('WARNING: Atomic index larger than maximum in line ' + line)
		if int(signal) > int(data['N_SIGS']):
			print('WARNING: Signal index larger than maximum in line ' + line)
		if arg_width > max_const_width:
			print('NOTE: Argument value larger than maximum in line ' + line)
			print('Argument value will be truncated')
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
