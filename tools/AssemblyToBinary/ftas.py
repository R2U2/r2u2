#!/usr/bin/python

import sys
import re

TIMESTAMP_WIDTH = 32

def writeToFile(file, content):
	f = open(file, 'w')
	f.write(content)
	f.close
	
def toBinary(value, width):
	value = int(value) # parse string to integer first
	b = bin(value)[2:]
	
	while len(b) < width:
		b = "0" + b
			
	if len(b) > width:	
		print(value, "Error: does not fit into", width, "bits")
		b = b[0:width]
		
	return b

def parseOperand(op):
	o = op[0]
	c = ""
	
	if o == "a":	# load atomic
		c = c + "00"
	elif o == "p":	# pt address
		c = c + "11"
	elif o == "i":  # immediate
		c = c + "01"
	elif o == "s":	# subformula
		c = c + "10"
	else:
		print("Error in line", i)

	c = c + toBinary(int(op[1:]), 8)
	
	return c

i = 0
timestampAddr = 0
boxMemAddr = 0
untilMemAddr = 0
opcode = ""
ts = ""
	
print("Compile future time config")

header=re.compile("s*\d+:")

for line in sys.stdin:
	i = i + 1
	op = line.split()
	if(header.match(op[0])):
		op.remove(op[0])
	# operation
	if op[0] == "and":
		opcode = opcode + "10101"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + parseOperand(op[2])
		opcode = opcode + "0000000"
		opcode = opcode + "00000000"
	
	elif op[0] == "load_ft" or op[0] == "load":
		opcode = opcode + "11100"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + "0000000000"
		opcode = opcode + "0000000"
		opcode = opcode + "00000000"

	elif op[0] == "impl":
		opcode = opcode + "11011"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + parseOperand(op[2])
		opcode = opcode + "0000000"
		opcode = opcode + "00000000"
				
	elif op[0] == "not":
		opcode = opcode + "10100"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + "0000000000"
		opcode = opcode + "0000000"
		opcode = opcode + "00000000"
		
	elif op[0] == "end":
		opcode = opcode + "11111"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + "0000000000"
		opcode = opcode + "0000000"
		opcode = opcode + "00000000"
		
	elif op[0] == "boxbox":
		opcode = opcode + "10110"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + "0000000000"
		opcode = opcode + toBinary(timestampAddr, 8)
		opcode = opcode + toBinary(boxMemAddr, 7)
		boxMemAddr = boxMemAddr + 1
		timestampAddr = timestampAddr + 1
		ts = ts + toBinary(op[2], 2*TIMESTAMP_WIDTH) + "\n"
		
	elif op[0] == "boxdot":
		opcode = opcode + "10111"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + "0000000000"
		opcode = opcode + toBinary(timestampAddr, 8)
		opcode = opcode + toBinary(boxMemAddr, 7)
		boxMemAddr = boxMemAddr + 1
		timestampAddr = timestampAddr + 1
		ts = ts + toBinary(op[2], TIMESTAMP_WIDTH) + toBinary(op[3], TIMESTAMP_WIDTH) + "\n"
		
	elif op[0] == "diamonddiamond":
		opcode = opcode + "11000"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + "0000000000"
		opcode = opcode + toBinary(timestampAddr, 8)
		opcode = opcode + toBinary(boxMemAddr, 7)
		boxMemAddr = boxMemAddr + 1
		timestampAddr = timestampAddr + 1
		ts = ts + toBinary(op[2], 2*TIMESTAMP_WIDTH) + "\n"
		
	elif op[0] == "diamonddot":
		opcode = opcode + "11001"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + "0000000000"
		opcode = opcode + toBinary(timestampAddr, 8)
		opcode = opcode + toBinary(boxMemAddr, 7)
		boxMemAddr = boxMemAddr + 1
		timestampAddr = timestampAddr + 1
		ts = ts + toBinary(op[2], TIMESTAMP_WIDTH) + toBinary(op[3], TIMESTAMP_WIDTH) + "\n"
		
	elif op[0] == "until":
		opcode = opcode + "11010"
		opcode = opcode + parseOperand(op[1])
		opcode = opcode + parseOperand(op[2])
		opcode = opcode + toBinary(timestampAddr, 8)
		opcode = opcode + toBinary(untilMemAddr, 7)
		untilMemAddr = untilMemAddr + 1
		timestampAddr = timestampAddr + 1
		ts = ts + toBinary(op[3], TIMESTAMP_WIDTH) + toBinary(op[4], TIMESTAMP_WIDTH) + "\n"
		
	else:
		print("Error in line", i, "(", op, ")")
		continue
	
	opcode = opcode + "\n"

writeToFile(sys.argv[1] + ".ftm", opcode)
writeToFile(sys.argv[1] + ".fti", ts)
	
#print opcode
#print ts
