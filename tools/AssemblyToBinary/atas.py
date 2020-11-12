import sys
import os
import re

def writeToFile(file, content):
	f = open(file, 'w')
	f.write(content)
	f.close

def toBinary(value, width):
	#print(value)
	value = int(value) # parse string to integer first

	b = bin(value)[2:]

	while len(b) < width:
		b = "0" + b

	if len(b) > width:
		print(value, "Error: does not fit into", width, "bits")
		b = b[0:width]

	return b

print('Compile atomic checker')

f = open(sys.argv[1])

binary = ''
for line in f:
	instr = line.split()

	atomic = re.search('\d+', instr[0])
	filter = instr[1]
	signal = instr[2]
	cond = instr[3]
	const = instr[4]

	if atomic is None:
		print("Error: atomic not valid in instruction " + line)
	else:
		binary += toBinary(atomic.group(), 8)

	if filter == "bool":
		binary += "0000"
	elif filter == "int":
		binary += "0001"
	elif filter == "double":
		binary += "0010"
	elif filter == "rate":
		binary += "0011"
	else:
		print("Error: filter is not valid in instruction " + line)

	binary += toBinary(signal, 8)

	if cond == ">":
		binary += "000"
	elif cond == "<":
		binary += "001"
	elif cond == "==":
		binary += "010"
	elif cond == ">=":
		binary += "011"
	elif cond == "<=":
		binary += "100"

	binary + toBinary(const, 32) # Max width is 32 bit constant

# Check to see if the '../binary_files' directory exists; if not make, the file
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__+'../binary_files/'
if(not os.path.isdir(__DirBinaryPath__)):
	os.mkdir(__DirBinaryPath__)

writeToFile(__DirBinaryPath__+'at.bin', binary)
