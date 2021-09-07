import sys
import os
import re

from .config import data

def toBinary(value, width):
	# Try for an integer (Chris)
	try:
		value = int(value)

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

		if len(b) > width:
			print(value, "Error: does not fit into ", width, " bits")
			b = b[0:width]

		return b

	# If not an integer, try float
	except ValueError:
		# Sources for Code:
		# https://www.geeksforgeeks.org/python-program-to-convert-floating-to-binary/
		# https://www.geeksforgeeks.org/ieee-standard-754-floating-point-numbers/

		# set up constants for widths
		if(width == 32):
			bias = 127
			exp_width = 8
			mantissa_width = 23
		if(width == 64):
			bias = 1023
			exp_width = 11
			mantissa_width = 52

		value = float(value)

		# sign of the float
		if(value < 0):
			sign = '1'
			value = value*-1
		else:
			sign = '0'

		# write in base 2 scientific notation
		exp = 0
		while(not( 1 <= value and value < 2)):
			if(value < 1):
				value *= 2
				exp -= 1
			elif(value >= 2):
				value /= 2
				exp += 1

		# put exp into binary
		exp = bin(exp + bias)
		exp = exp[2:len(exp)]
		# if too short, pad with zeros at start
		while(len(exp) < exp_width):
			exp = '0' + exp
		# if too long, take most significant bits
		if(len(exp) > exp_width):
			exp = exp[0:exp_width]

		value -= 1
		#approximate the fraction
		mantissa = ''
		for val in range(0, mantissa_width):
			if(str(value) == '0'):
				mantissa += 0
			elif(str(value) == '1'):
				mantissa += '1'
				value = 0
			else:
				while(value > 1):
					value /= 10
				value *= 2
				w, d = str(value).split('.')
				mantissa += w
				value = float(d)

		return sign+exp+mantissa

def assemble(f):
	binary = ""

	max_at_width = int(data['L_ATOMIC_ADDR'])
	max_sig_width = int(data['L_SIG_ADDR'])
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
			print("ERROR: atomic not valid in instruction " + line)
			binary += "00000000"
		else:
			binary += toBinary(atomic, max_at_width)

		if filter == "bool":
			binary += "0001"
		elif filter == "int":
			binary += "0010"
		elif filter == "float":
			binary += "0011"
		elif filter == "rate":
			binary += "0100"
		elif filter == "abs_diff_angle":
			binary += "0101"
		elif filter == "movavg":
			binary += "0110"
		else:
			print("ERROR: filter is not valid in instruction " + line)
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

		binary += "\\n"

		# Give warning if specs do not fit in desired configuration
		arg_width = int.bit_length(int(arg))
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
