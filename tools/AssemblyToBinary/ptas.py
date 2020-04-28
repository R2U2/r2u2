#------------------------------------------------------------------------------#
# Author: Matt Cauwels
# Date: April 21st, 2020
# File Name: ptas.py (short for Past-Time Assembler)
# Description:

#------------------------------------------------------------------------------#
#!/usr/bin/python
import os
import sys
import re
# usage: python ftas.py [assembly file name] [TIMESTAMP_BYTE_extend_byte]
#from config import TIMESTAMP_BYTE_extend_byte
TIMESTAMP_BYTE_extend_byte = int(sys.argv[2])
TIMESTAMP_WIDTH = 8*TIMESTAMP_BYTE_extend_byte
#------------------------------------------------------------------------------#
# Mapping from OP Codes to Variables
#------------------------------------------------------------------------------#
# R2U2 Operations
OP_START        = "01011"
OP_FT_LOD       = "11100"
OP_END          = "01100"
OP_END_SEQUENCE = "11111"
# Propositional Operators
OP_NOT          = "00011"
OP_AND          = "00100"
OP_OR           = "00101"
OP_IMPL         = "00110"
OP_EQUIVALENT   = "00111"
# Unbounded Past-Time Operators
OP_PT_Y  = "01000"
OP_PT_O  = "01001"
OP_PT_H  = "01010"
OP_PT_S  = "01110"
# Explicitly Bounded Past-Time Operators
OP_PT_HJ = "10010"
OP_PT_OJ = "10000"
OP_PT_SJ = "10011"
# Implicitly Bounded Past-Time Operators
OP_PT_HT = "10001"
OP_PT_OT = "01111"


#------------------------------------------------------------------------------#
# Method for writing files
#------------------------------------------------------------------------------#
def writeToFile(file, content):
    f = open(file, 'w')
    f.write(content)
    f.close
#------------------------------------------------------------------------------#
# Method for
#------------------------------------------------------------------------------#
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
#------------------------------------------------------------------------------#
#
#------------------------------------------------------------------------------#
def parseOperand(op):
    c = ""
    if(op=='TRUE'):
        c = c + "01"+toBinary(1, 8)
    elif(op=='FALSE'):
        c = c + "01"+toBinary(0, 8)
    else:
        o = op[0]
        if o == "a":    # load atomic
            c = c + "00"
        elif o == "p":    # pt address, not set
            c = c + "11"
        elif o == "i":  # immediate, direct
            c = c + "01"
        elif o == "s":    # subformula
            c = c + "10"
        else:
            print("Error in specifying input type, did you use any weird atomic names?", i)

        c = c + toBinary(int(op[1:]), 8)
    return c

i = 0
timestampAddr = 0
hisMemAddr = 0
onceMemAddr = 0
sinceMemAddr = 0
opcode = ""
ts = ""

print("Compile past time config")

header=re.compile("s*\d+:")

f = open(sys.argv[1])

#------------------------------------------------------------------------------#
# R2U2 Operations
#------------------------------------------------------------------------------#
for line in f:
    i = i + 1
    op = line.split()
    if(header.match(op[0])):
        op.remove(op[0])

    # Uncomment for troubleshooting
    #print(op)

    #--------------------------------------------------------------------------#
    # R2U2 Operations
    #--------------------------------------------------------------------------#
    # Load Atomic
    if op[0] == "load_ft" or op[0] == "load":
        opcode = opcode + OP_FT_LOD
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + "0000000000"
        opcode = opcode + "0000000"
        opcode = opcode + "00000000"
    # End of Assembly Code
    elif ((op[0] == "end") and (op[1] == "sequence")):
        opcode = opcode + OP_END_SEQUENCE
        opcode = opcode + "01" + toBinary(0,8)
        opcode = opcode + "0000000000"
        opcode = opcode + "0000000"
        opcode = opcode + "00000000"
    # End of Formula
    elif op[0] == "end":
        opcode = opcode + OP_END
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + toBinary(op[2],10)
        opcode = opcode + "0000000"
        opcode = opcode + "00000000"
    #--------------------------------------------------------------------------#
    # Propositional Operators
    #--------------------------------------------------------------------------#
    # Conjunction (AND)
    elif op[0] == "and":
        opcode = opcode + OP_AND
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + parseOperand(op[2])
        opcode = opcode + "0000000"
        opcode = opcode + "00000000"
    # Disjunction (OR)
    elif op[0] == "or":
        opcode = opcode + OP_OR
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + parseOperand(op[2])
        opcode = opcode + "0000000"
        opcode = opcode + "00000000"
    # Implies
    elif op[0] == "impl":
        opcode = opcode + OP_IMPL
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + parseOperand(op[2])
        opcode = opcode + "0000000"
        opcode = opcode + "00000000"
    # Negation (NOT)
    elif op[0] == "not":
        opcode = opcode + OP_NOT
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + "0000000000"
        opcode = opcode + "0000000"
        opcode = opcode + "00000000"

    #--------------------------------------------------------------------------#
    # Past-Time Temporal Operators
    #--------------------------------------------------------------------------#
    # NOTE: Still need to implement past-time! Double-check what is written now.
    #    - First line of opcode was from R2U2_SW/R2U2_C/TL/TL_observers.h file
    # Yesterday
    elif op[0] == "yesterday":
        opcode = opcode + OP_PT_Y
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + "0000000000"
        opcode = opcode + toBinary(timestampAddr, 8)
        opcode = opcode + toBinary(hisMemAddr, 7)
        hisMemAddr = hisMemAddr + 1
        timestampAddr = timestampAddr + 1
        ts = ts + toBinary(1, 2*TIMESTAMP_WIDTH) + '\n'
    # Historically with single time point (H[t1,t2])
    elif op[0] == "his": #"boxbox-interval":
        opcode = opcode + OP_PT_HJ
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + "0000000000"
        opcode = opcode + toBinary(timestampAddr, 8)
        opcode = opcode + toBinary(hisMemAddr, 7)
        hisMemAddr = hisMemAddr + 1
        timestampAddr = timestampAddr + 1
        ts = ts + toBinary(op[2], TIMESTAMP_WIDTH) + toBinary(op[3], TIMESTAMP_WIDTH) + '\n'
    # Historically with interval (H[t])
    elif op[0] == "his_impl":
        opcode = opcode + OP_PT_HT
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + "0000000000"
        opcode = opcode + toBinary(timestampAddr, 8)
        opcode = opcode + toBinary(hisMemAddr, 7)
        hisMemAddr = hisMemAddr + 1
        timestampAddr = timestampAddr + 1
        ts = ts + toBinary(op[2], 2*TIMESTAMP_WIDTH) + '\n'
    # Once with interval (O[t1,t2])
    elif op[0] == "once": #"diamonddiamond-interval":
        opcode = opcode + OP_PT_OJ
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + "0000000000"
        opcode = opcode + toBinary(timestampAddr, 8)
        opcode = opcode + toBinary(onceMemAddr, 7)
        onceMemAddr = onceMemAddr + 1
        timestampAddr = timestampAddr + 1
        ts = ts + toBinary(op[2], TIMESTAMP_WIDTH) + toBinary(op[3], TIMESTAMP_WIDTH) + '\n'
    # Once with interval (O[t])
    elif op[0] == "once_impl":
        opcode = opcode + OP_PT_OT
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + "0000000000"
        opcode = opcode + toBinary(timestampAddr, 8)
        opcode = opcode + toBinary(onceMemAddr, 7)
        onceMemAddr = onceMemAddr + 1
        timestampAddr = timestampAddr + 1
        ts = ts + toBinary(op[2], 2*TIMESTAMP_WIDTH) + '\n'
    # Since with interval (S[t1,t2])
    elif op[0] == "since":
        opcode = opcode + OP_PT_SJ
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + parseOperand(op[2])
        opcode = opcode + toBinary(timestampAddr, 8)
        opcode = opcode + toBinary(sinceMemAddr, 7)
        sinceMemAddr = sinceMemAddr + 1
        timestampAddr = timestampAddr + 1
        ts = ts + toBinary(op[3], TIMESTAMP_WIDTH) + toBinary(op[4], TIMESTAMP_WIDTH) + "\n"
    # Since with interval (S[t])
    elif op[0] == "since_impl":
        opcode = opcode + OP_PT_S
        opcode = opcode + parseOperand(op[1])
        opcode = opcode + parseOperand(op[2])
        opcode = opcode + toBinary(timestampAddr, 8)
        opcode = opcode + toBinary(sinceMemAddr, 7)
        sinceMemAddr = sinceMemAddr + 1
        timestampAddr = timestampAddr + 1
        ts = ts + toBinary(op[3], 2*TIMESTAMP_WIDTH) + "\n"
    # Else, it is not a valid operation.
    elif op[0] == "#":
        line = ""
        for i in range(0,len(op)):
            line = line + op[i] + " "
        print(line)
        continue
    # Else, it is not a valid operation.
    else:
        print("Error in line", i, "(", op, ")")
        continue


    opcode = opcode + "\n"
f.close()

# Check to see if the '../binary_files' directory exists; if not make, the file
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__ + '../binary_files/'
if(not os.path.isdir(__DirBinaryPath__)):
    os.mkdir(__DirBinaryPath__)

writeToFile(__DirBinaryPath__+'ptm.bin', opcode)
writeToFile(__DirBinaryPath__+'pti.bin', ts)

#print opcode
#print ts
