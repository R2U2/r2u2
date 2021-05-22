#!/usr/bin/python
import os
import sys
import re
# usage: python ftas.py [assembly file name] [TIMESTAMP_BYTE_extend_byte]
#from config import TIMESTAMP_BYTE_extend_byte

def toBinary(value, width):
	#print(value)
	value = int(value) # parse string to integer first

	b = bin(value)[2:]

	while len(b) < width:
		b = "0" + b

	if len(b) > width:
		print(value, "ERROR: does not fit into", width, "bits")
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
			print("ERROR: specifying input type, did you use any weird atomic names?", i)

		c = c + toBinary(int(op[1:]), 8)
	return c

def assemble(f, s, timestamp_width):
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
		#----------------------------------------------------------------------#
		# R2U2 Operations
		#----------------------------------------------------------------------#
		# Load Atomic
		if op[0] == "load_ft" or op[0] == "load":
			opcode += "11100"
			opcode += parseOperand(op[1])
			opcode += "0000000000"
			opcode += "0000000"
			opcode += "00000000"
		# End of Assembly Code
		elif ((op[0] == "end") and (op[1] == "sequence")):
			opcode += "11111"
			opcode += "01" + toBinary(0,8)
			opcode += "0000000000"
			opcode += "0000000"
			opcode += "00000000"
		# End of Formula
		elif op[0] == "end":
			opcode += "01100"
			opcode += parseOperand(op[1])
			opcode += "01" + toBinary(op[2],8)
			opcode += "0000000"
			opcode += "00000000"
		#----------------------------------------------------------------------#
		# Propositional Operators
		#----------------------------------------------------------------------#
		# Conjunction (AND)
		elif op[0] == "and":
			opcode += "10101"
			opcode += parseOperand(op[1])
			opcode += parseOperand(op[2])
			opcode += "0000000"
			opcode += "00000000"
		# Implies
		elif op[0] == "impl":
			opcode += "11011"
			opcode += parseOperand(op[1])
			opcode += parseOperand(op[2])
			opcode += "0000000"
			opcode += "00000000"
		# Negation (NOT)
		elif op[0] == "not":
			opcode += "10100"
			opcode += parseOperand(op[1])
			opcode += "0000000000"
			opcode += "0000000"
			opcode += "00000000"
		#----------------------------------------------------------------------#
		# Future-Time Temporal Operators
		#----------------------------------------------------------------------#
		# Global with single time point (G[t])
		elif op[0] == "boxbox":
			opcode += "10110"
			opcode += parseOperand(op[1])
			opcode += "0000000000"
			opcode += toBinary(timestampAddr, 8)
			opcode += toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts += toBinary(op[2], 2*timestamp_width) + "\\n"
		# Global with interval (G[t1,t2])
		elif op[0] == "boxdot":
			opcode += "10111"
			opcode += parseOperand(op[1])
			opcode += "0000000000"
			opcode += toBinary(timestampAddr, 8)
			opcode += toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts += toBinary(op[2], timestamp_width) + \
				toBinary(op[3], timestamp_width) + "\\n"
		# Eventually with single time point (F[t])
		elif op[0] == "diamonddiamond":
			opcode += "11000"
			opcode += parseOperand(op[1])
			opcode += "0000000000"
			opcode += toBinary(timestampAddr, 8)
			opcode += toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts += toBinary(op[2], 2*timestamp_width) + "\\n"
		# Eventually with interval (F[t1,t2])
		elif op[0] == "diamonddot":
			opcode += "11001"
			opcode += parseOperand(op[1])
			opcode += "0000000000"
			opcode += toBinary(timestampAddr, 8)
			opcode += toBinary(boxMemAddr, 7)
			boxMemAddr = boxMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts += toBinary(op[2], timestamp_width) + \
				toBinary(op[3], timestamp_width) + "\\n"
		# Until with interval (U[t1,t2])
		elif op[0] == "until":
			opcode += "11010"
			opcode += parseOperand(op[1])
			opcode += parseOperand(op[2])
			opcode += toBinary(timestampAddr, 8)
			opcode += toBinary(untilMemAddr, 7)
			untilMemAddr = untilMemAddr + 1
			timestampAddr = timestampAddr + 1
			ts += toBinary(op[3], timestamp_width) + \
				toBinary(op[4], timestamp_width) + "\\n"
		# Else, it is not a valid operation.
		else:
			print("ERROR: line ", i, "(", op, ")")
			continue

		opcode += "\\n"

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

def assemble_ft(ftasm, ftscqasm, ts_ext, gen_dir, no_binaries):
	print('Assembling FT')

	f = open(ftasm, 'r')
	if not os.path.isfile(ftscqasm):
		s = ""
	else:
		s = open(ftscqasm, 'r')
	timestamp_width = 8 * int(ts_ext)
	bin_dir = gen_dir+'binary_files/'
	if(not os.path.isdir(bin_dir)):
		os.mkdir(bin_dir)

	opcode, ts, scq = assemble(f, s, timestamp_width)

	f.close()
	s.close()

	if no_binaries == 'True':
		global prog_text
		prog_text += opcode + "\";\n"
		prog_text += "char *fti_bin = \"" + ts + "\";\n"
		prog_text += "char *ftscq_bin = \"" + scq + "\";\n"
		with open(gen_dir+'config.c', 'w') as c:
			c.write(prog_text)
	else:
		with open(bin_dir+'ftm.bin', 'w') as ftm:
			ftm.write(opcode.replace('\\n','\n'))
		with open(bin_dir+'fti.bin', 'w') as fti:
			fti.write(ts.replace('\\n','\n'))
		with open(bin_dir+'ftscq.bin', 'w') as ftscq:
			ftscq.write(scq.replace('\\n','\n'))
