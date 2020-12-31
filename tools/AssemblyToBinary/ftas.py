#!/usr/bin/python
import os
import sys
import re
# usage: python ftas.py [assembly file name] [TIMESTAMP_BYTE_extend_byte]
#from config import TIMESTAMP_BYTE_extend_byte
TIMESTAMP_BYTE_extend_byte = int(sys.argv[3])
TIMESTAMP_WIDTH = 8*TIMESTAMP_BYTE_extend_byte

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__ + '../binary_files/'

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

def parseOperand(op):
	c = ""
	if(op=='TRUE'):
		c = c + "01"+toBinary(1, 8)
	elif(op=='FALSE'):
		c = c + "01"+toBinary(0, 8)
	else:
		o = op[0]
		if o == "a":	# load atomic
			c = c + "00"
		elif o == "p":	# pt address, not set
			c = c + "11"
		elif o == "i":  # immediate, direct
			c = c + "01"
		elif o == "s":	# subformula
			c = c + "10"
		else:
			print("Error in specifying input type, did you use any weird atomic names?", i)

		c = c + toBinary(int(op[1:]), 8)
	return c

def assemble(f, s):
	i = 0
	timestampAddr = 0
	boxMemAddr = 0
	untilMemAddr = 0
	opcode = ""
	ts = ""
	header=re.compile("s*\d+:")
	for line in f:
		i = i + 1
		op = line.split()
		if(header.match(op[0])):
			op.remove(op[0])
		#-------------------------------------------------------------------------------#
		# R2U2 Operations
		#-------------------------------------------------------------------------------#
		# Load Atomic
		if op[0] == "load_ft" or op[0] == "load":
			opcode = opcode + "11100"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + "0000000000"
			opcode = opcode + "0000000"
			opcode = opcode + "00000000"
		# End of Assembly Code
		elif ((op[0] == "end") and (op[1] == "sequence")):
			opcode = opcode + "11111"
			opcode = opcode + "01" + toBinary(0,8)
			opcode = opcode + "0000000000"
			opcode = opcode + "0000000"
			opcode = opcode + "00000000"
		# End of Formula
		elif op[0] == "end":
			opcode = opcode + "01100"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + "01" + toBinary(op[2],8)
			opcode = opcode + "0000000"
			opcode = opcode + "00000000"
		#-------------------------------------------------------------------------------#
		# Propositional Operators
		#-------------------------------------------------------------------------------#
		# Conjunction (AND)
		elif op[0] == "and":
			opcode = opcode + "10101"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + parseOperand(op[2])
			opcode = opcode + "0000000"
			opcode = opcode + "00000000"
		# Implies
		elif op[0] == "impl":
			opcode = opcode + "11011"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + parseOperand(op[2])
			opcode = opcode + "0000000"
			opcode = opcode + "00000000"
		# Negation (NOT)
		elif op[0] == "not":
			opcode = opcode + "10100"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + "0000000000"
			opcode = opcode + "0000000"
			opcode = opcode + "00000000"
		#-------------------------------------------------------------------------------#
		# Future-Time Temporal Operators
		#-------------------------------------------------------------------------------#
		# Global with single time point (G[t])
		elif op[0] == "boxbox":
			opcode = opcode + "10110"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + "0000000000"
			opcode = opcode + toBinary(timestampAddr, 8)
			opcode = opcode + toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts = ts + toBinary(op[2], 2*TIMESTAMP_WIDTH) + "\\n"
		# Global with interval (G[t1,t2])
		elif op[0] == "boxdot":
			opcode = opcode + "10111"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + "0000000000"
			opcode = opcode + toBinary(timestampAddr, 8)
			opcode = opcode + toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts = ts + toBinary(op[2], TIMESTAMP_WIDTH) + toBinary(op[3], TIMESTAMP_WIDTH) + "\\n"
		# Eventually with single time point (F[t])
		elif op[0] == "diamonddiamond":
			opcode = opcode + "11000"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + "0000000000"
			opcode = opcode + toBinary(timestampAddr, 8)
			opcode = opcode + toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts = ts + toBinary(op[2], 2*TIMESTAMP_WIDTH) + "\\n"
		# Eventually with interval (F[t1,t2])
		elif op[0] == "diamonddot":
			opcode = opcode + "11001"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + "0000000000"
			opcode = opcode + toBinary(timestampAddr, 8)
			opcode = opcode + toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts = ts + toBinary(op[2], TIMESTAMP_WIDTH) + toBinary(op[3], TIMESTAMP_WIDTH) + "\\n"
		# Until with interval (U[t1,t2])
		elif op[0] == "until":
			opcode = opcode + "11010"
			opcode = opcode + parseOperand(op[1])
			opcode = opcode + parseOperand(op[2])
			opcode = opcode + toBinary(timestampAddr, 8)
			opcode = opcode + toBinary(untilMemAddr, 7)
			untilMemAddr = untilMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts = ts + toBinary(op[3], TIMESTAMP_WIDTH) + toBinary(op[4], TIMESTAMP_WIDTH) + "\\n"
		# Else, it is not a valid operation.
		else:
			print("Error in line", i, "(", op, ")")
			continue

		opcode = opcode + "\\n"

	scq = ""
	for line in s:
		pos = line.split()
		st_pos = int(pos[0])
		ed_pos = int(pos[1])
		scq += '{0:016b}'.format(st_pos)+'{0:016b}'.format(ed_pos)+'\\n'

	return opcode, ts, scq

prog_text = \
"""
#include "TL_observers.h"
char *ftm_bin = "
""".strip()

if __name__ == '__main__':
	print("Compile past time config")
	f = open(sys.argv[1])
	s = open(sys.argv[2])
	opt = sys.argv[4]
	if(not os.path.isdir(__DirBinaryPath__)):
		os.mkdir(__DirBinaryPath__)
	opcode, ts, scq = assemble(f, s)
	if opt == 'True':
		prog_text += opcode + "\";\n"
		prog_text += "char *fti_bin = \"" + ts + "\";\n"
		prog_text += "char *ftscq_bin = \"" + scq + "\";\n"
		writeToFile(__DirBinaryPath__+'ft.c', prog_text)
	else:
		writeToFile(__DirBinaryPath__+'ftm.bin', opcode.replace('\\n','\n'))
		writeToFile(__DirBinaryPath__+'fti.bin', ts.replace('\\n','\n'))
		writeToFile(__DirBinaryPath__+'ftscq.bin', scq.replace('\\n','\n'))
	f.close()
	s.close()
