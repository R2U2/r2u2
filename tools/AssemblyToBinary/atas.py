import sys
import os
import re

def writeToFile(file, content):
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

print('Assemble atomic checker')

f = open(sys.argv[1])

binary = ''
for line in f:
	if re.fullmatch('\s*', line):
		break

	instr = line.split()

	atomic = instr[0][1:]
	filter = instr[1]
	signal = instr[2][1:]
	arg    = instr[3]
	cond   = instr[4]
	comp   = instr[5]

	if atomic is None:
		print("Error: atomic not valid in instruction " + line)
		binary += "00000000"
	else:
		binary += toBinary(atomic, 8)

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

	binary += "\n"

# Check to see if the '../binary_files' directory exists; if not make, the file
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__+'../binary_files/'
if(not os.path.isdir(__DirBinaryPath__)):
	os.mkdir(__DirBinaryPath__)

writeToFile(__DirBinaryPath__+'at.bin', binary)
