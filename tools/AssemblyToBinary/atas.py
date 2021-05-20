import sys
import os
import re

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__+'../binary_files/'

def writeToFile(file, content):
	f = open(file, 'w')
	f.write(content)
	f.close

def appendToFile(file, content):
	f = open(file, 'a')
	f.write(content)
	f.close

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
	for line in f:
		if re.fullmatch('\s*', line):
			break

		instr = line.split()

		atomic = instr[0][1:-1]
		filter = instr[1]
		signal = instr[2][1:]
		arg    = instr[3]
		cond   = instr[4]
		comp  = instr[5]

		if atomic is None:
			print("Error: atomic not valid in instruction " + line)
			binary += "00000000"
		else:
			binary += toBinary(atomic, 8)

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
			print("Error: filter is not valid in instruction " + line)
			binary += "0000"

		binary += toBinary(signal, 8)
		binary += toBinary(arg, 32)

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
			binary += toBinary(comp[1:], 32) # Max width is 32 bit constant
		else:
			binary += "0"
			binary += toBinary(comp, 32) # Max width is 32 bit constant

		binary += "\\n"

	return binary

prog_text = \
"""
#include "at_globals.h"
char *at_bin = "
""".strip()

if __name__ == '__main__':
	print('Assemble atomic checker')
	if(not os.path.isdir(__DirBinaryPath__)):
		os.mkdir(__DirBinaryPath__)
	f = open(sys.argv[1])
	opt = sys.argv[2]
	binary = assemble(f)
	if opt == 'True':
		prog_text += binary + "\";"
		appendToFile(__DirBinaryPath__+'config.c', prog_text)
	else:
		writeToFile(__DirBinaryPath__+'at.bin', binary.replace('\\n','\n'))
