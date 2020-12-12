import sys
import os
import re

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__+'../binary_files/'

def writeToFile(file, content):
	# Check to see if the '../binary_files' directory exists; if not make, the file
	if(not os.path.isdir(__DirBinaryPath__)):
		os.mkdir(__DirBinaryPath__)
	f = open(file, 'w')
	f.write(content)
	f.close

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

	if len(b) > width:
		print(value, "Error: does not fit into ", width, " bits")
		b = b[0:width]

	return b

def assemble_binary(f):
	binary = ''
	for line in f:
		if re.fullmatch('\s*', line):
			break

		instr = line.split()

		atomic = re.search('\d+', instr[0])
		filter = instr[1]
		signal = instr[2]
		arg    = instr[3]
		comp   = instr[4]
		const  = instr[5]

		if atomic is None:
			print("Error: atomic not valid in instruction " + line)
			binary += "00000000"
		else:
			binary += toBinary(atomic.group(), 8)

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

		binary += toBinary(signal, 8)
		binary += toBinary(arg, 32)

		if comp == "==":
			binary += "000"
		elif comp == "!=":
			binary += "001"
		elif comp == "<":
			binary += "010"
		elif comp == "<=":
			binary += "011"
		elif comp == ">":
			binary += "100"
		elif comp == ">=":
			binary += "101"
		else:
			print("Error: comparison operator is not valid in instruction " + line)
			binary += "111"

		binary += toBinary(const, 32) # Max width is 32 bit constant

		binary += "\n"

	return binary

def assemble_c(f):
	prog_text = \
	"""
	#include <stdint.h>
	#include <stdbool.h>

	#include "at_instruction.h"
	#include "at_globals.h"
	#include "filters/filter_rate.h"
	#include "filters/filter_movavg.h"

	void populate_at_instr() {
	"""
	num_instr = 0
	for line in f:
		if re.fullmatch('\s*', line):
			break

		instr = line.split()

		atomic = re.search('\d+', instr[0])
		filter = instr[1]
		signal = instr[2]
		arg    = instr[3]
		comp   = instr[4]
		const  = instr[5]

		if atomic is None:
			print("Error: atomic not valid in instruction " + line)
			prog_text += "at_instructions[" + str(num_instr) + "].atom_addr = 0;\n"
		else:
			prog_text += "at_instructions[" + str(num_instr) + "].atom_addr = " + \
				atomic.group() + ";\n"

		if filter == "bool":
			prog_text += "at_instructions[" + str(num_instr) + "].filter = 1;\n"
			prog_text += "at_instructions[" + str(num_instr) + "].comp_const.b = (bool) " \
				+ const + ";\n"
		elif filter == "int":
			prog_text += "at_instructions[" + str(num_instr) + "].filter = 2;\n"
			prog_text += "at_instructions[" + str(num_instr) + "].comp_const.i = " \
				+ const + ";\n"
		elif filter == "double":
			prog_text += "at_instructions[" + str(num_instr) + "].filter = 3;\n"
			prog_text += "at_instructions[" + str(num_instr) + "].comp_const.d = " \
				+ const + ";\n"
		elif filter == "rate":
			prog_text += "at_instructions[" + str(num_instr) + "].filter = 4;\n"
			prog_text += "at_instructions[" + str(num_instr) + "].comp_const.d = " \
				+ const + ";\n"
		elif filter == "abs_diff_angle":
			prog_text += "at_instructions[" + str(num_instr) + "].filter = 5;\n"
			prog_text += "at_instructions[" + str(num_instr) + "].comp_const.d = " \
				+ const + ";\n"
			prog_text += "at_instructions[" + str(num_instr) + "].filt_data_struct.diff_angle" \
				+ " = " + arg + ";\n"
		elif filter == "movavg":
			prog_text += "at_instructions[" + str(num_instr) + "].filter = 6;\n"
			prog_text += "at_instructions[" + str(num_instr) + "].comp_const.d = " \
				+ const + ";\n"
			prog_text += "at_instructions[" + str(num_instr) + "].filt_data_struct.movavg" \
				+ " = filter_movavg_init((uint16_t)" + arg + ");\n"
		else:
			print("Error: filter is not valid in instruction " + line)
			prog_text += "at_instructions[" + str(num_instr) + "].filter = 1\n"

		prog_text += "at_instructions[" + str(num_instr) + "].sig_addr = " + signal + ";\n"

		if comp == "==":
			prog_text += "at_instructions[" + str(num_instr) + "].comp = 0;\n"
		elif comp == "!=":
			prog_text += "at_instructions[" + str(num_instr) + "].comp = 1;\n"
		elif comp == "<":
			prog_text += "at_instructions[" + str(num_instr) + "].comp = 2;\n"
		elif comp == "<=":
			prog_text += "at_instructions[" + str(num_instr) + "].comp = 3;\n"
		elif comp == ">":
			prog_text += "at_instructions[" + str(num_instr) + "].comp = 4;\n"
		elif comp == ">=":
			prog_text += "at_instructions[" + str(num_instr) + "].comp = 5;\n"
		else:
			print("Error: comparison operator is not valid in instruction " + line)
			prog_text += "at_instructions[" + str(num_instr) + "].comp = 7;\n"

		prog_text += "\n"
		num_instr += 1

	prog_text += "num_instr = " + str(num_instr) + ";\n}"

	return prog_text.strip()

header = \
"""
#ifndef AT_STRUCTS_H
#define AT_STRUCTS_H
void populate_at_instr();
#endif
""".strip()

if __name__ == '__main__':
	print('Assemble atomic checker')
	f = open(sys.argv[1])
	opt = sys.argv[2]
	if opt == 'no-files':
		data = assemble_c(f)
		writeToFile(__DirBinaryPath__+'at_structs.h', header)
		writeToFile(__DirBinaryPath__+'at_structs.c', data)
	else:
		data = assemble_binary(f)
		writeToFile(__DirBinaryPath__+'at.bin', data)
