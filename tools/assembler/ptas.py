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
OP_PT_YESTERDAY  = "01000"
OP_PT_ONCE  = "01001"
OP_PT_HISTORICALLY  = "01010"
OP_PT_SINCE  = "01110"
# Explicitly Bounded Past-Time Operators
OP_PT_HISTORICALLY_INTERVAL = "10010"
OP_PT_ONCE_INTERVAL = "10000"
OP_PT_SINCE_INTERVAL = "10011"
# Implicitly Bounded Past-Time Operators
OP_PT_HISTORICALLY_TIMEPOINT = "10001"
OP_PT_ONCE_TIMEPOINT = "01111"

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
        print(value, "ERROR: does not fit into", width, "bits")
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
            print("ERROR: specifying input type, did you use any weird atomic names?", i)

        c = c + toBinary(int(op[1:]), 8)
    return c

def assemble(f, timestamp_width):
    i = 0
    timestampAddr = 0
    hisMemAddr = 0
    onceMemAddr = 0
    sinceMemAddr = 0
    opcode = ""
    ts = ""
    header=re.compile("s*\d+:")

    #--------------------------------------------------------------------------#
    # R2U2 Operations
    #--------------------------------------------------------------------------#
    for line in f.splitlines():
        i = i + 1
        op = line.split()
        if(header.match(op[0])):
            op.remove(op[0])

        # Uncomment for troubleshooting
        #print(op)

        #----------------------------------------------------------------------#
        # R2U2 Operations
        #----------------------------------------------------------------------#
        # Load Atomic
        if op[0] == "load_ft" or op[0] == "load":
            opcode += OP_FT_LOD
            opcode += parseOperand(op[1])
            opcode += "0000000000"
            opcode += "0000000"
            opcode += "00000000"
        # End of Assembly Code
        elif ((op[0] == "end") and (op[1] == "sequence")):
            opcode += OP_END_SEQUENCE
            opcode += "01" + toBinary(0,8)
            opcode += "0000000000"
            opcode += "0000000"
            opcode += "00000000"
        # End of Formula
        elif op[0] == "end":
            opcode += OP_END
            opcode += parseOperand(op[1])
            opcode += "01" + toBinary(op[2],8)
            opcode += "0000000"
            opcode += "00000000"
        #----------------------------------------------------------------------#
        # Propositional Operators
        #----------------------------------------------------------------------#
        # Conjunction (AND)
        elif op[0] == "and":
            opcode += OP_AND
            opcode += parseOperand(op[1])
            opcode += parseOperand(op[2])
            opcode += "0000000"
            opcode += "00000000"
        # Disjunction (OR)
        elif op[0] == "or":
            opcode += OP_OR
            opcode += parseOperand(op[1])
            opcode += parseOperand(op[2])
            opcode += "0000000"
            opcode += "00000000"
        # Implies
        elif op[0] == "impl":
            opcode += OP_IMPL
            opcode += parseOperand(op[1])
            opcode += parseOperand(op[2])
            opcode += "0000000"
            opcode += "00000000"
        # Negation (NOT)
        elif op[0] == "not":
            opcode += OP_NOT
            opcode += parseOperand(op[1])
            opcode += "0000000000"
            opcode += "0000000"
            opcode += "00000000"

        #----------------------------------------------------------------------#
        # Past-Time Temporal Operators
        #----------------------------------------------------------------------#
        # NOTE: Still need to implement past-time! Double-check what is written now.
        #    - First line of opcode was from R2U2_C/TL/TL_observers.h file
        # Yesterday
        elif op[0] == "yesterday":
            opcode = opcode + OP_PT_YESTERDAY
            opcode = opcode + parseOperand(op[1])
            opcode = opcode + "0000000000"
            opcode = opcode + toBinary(timestampAddr, 8)
            opcode = opcode + toBinary(hisMemAddr, 7)
            hisMemAddr = hisMemAddr + 1
            timestampAddr = timestampAddr + 1
            ts += toBinary(1, 2*timestamp_width) + '\\n'
        # Historically with single time point (H[t1,t2])
        elif op[0] == "his": #"boxbox-interval":
            opcode = opcode + OP_PT_HISTORICALLY_INTERVAL
            opcode = opcode + parseOperand(op[1])
            opcode = opcode + "0000000000"
            opcode = opcode + toBinary(timestampAddr, 8)
            opcode = opcode + toBinary(hisMemAddr, 7)
            hisMemAddr = hisMemAddr + 1
            timestampAddr = timestampAddr + 1
            ts += toBinary(op[2], timestamp_width) + toBinary(op[3], timestamp_width) + '\\n'
        # Historically with interval (H[t])
        elif op[0] == "his_impl":
            opcode = opcode + OP_PT_HISTORICALLY_TIMEPOINT
            opcode = opcode + parseOperand(op[1])
            opcode = opcode + "0000000000"
            opcode = opcode + toBinary(timestampAddr, 8)
            opcode = opcode + toBinary(hisMemAddr, 7)
            hisMemAddr = hisMemAddr + 1
            timestampAddr = timestampAddr + 1
            ts += toBinary(op[2], 2*timestamp_width) + '\\n'
        # Once with interval (O[t1,t2])
        elif op[0] == "once": #"diamonddiamond-interval":
            opcode = opcode + OP_PT_ONCE_INTERVAL
            opcode = opcode + parseOperand(op[1])
            opcode = opcode + "0000000000"
            opcode = opcode + toBinary(timestampAddr, 8)
            opcode = opcode + toBinary(onceMemAddr, 7)
            onceMemAddr = onceMemAddr + 1
            timestampAddr = timestampAddr + 1
            ts += toBinary(op[2], timestamp_width) + toBinary(op[3], timestamp_width) + '\\n'
        # Once with interval (O[t])
        elif op[0] == "once_impl":
            opcode = opcode + OP_PT_ONCE_TIMEPOINT
            opcode = opcode + parseOperand(op[1])
            opcode = opcode + "0000000000"
            opcode = opcode + toBinary(timestampAddr, 8)
            opcode = opcode + toBinary(onceMemAddr, 7)
            onceMemAddr = onceMemAddr + 1
            timestampAddr = timestampAddr + 1
            ts += toBinary(op[2], 2*timestamp_width) + '\\n'
        # Since with interval (S[t1,t2])
        elif op[0] == "since":
            opcode = opcode + OP_PT_SINCE_INTERVAL
            opcode = opcode + parseOperand(op[1])
            opcode = opcode + parseOperand(op[2])
            opcode = opcode + toBinary(timestampAddr, 8)
            opcode = opcode + toBinary(sinceMemAddr, 7)
            sinceMemAddr = sinceMemAddr + 1
            timestampAddr = timestampAddr + 1
            ts += toBinary(op[3], timestamp_width) + toBinary(op[4], timestamp_width) + "\\n"
        # Since with interval (S[t])
        elif op[0] == "since_impl":
            opcode = opcode + OP_PT_SINCE
            opcode = opcode + parseOperand(op[1])
            opcode = opcode + parseOperand(op[2])
            opcode = opcode + toBinary(timestampAddr, 8)
            opcode = opcode + toBinary(sinceMemAddr, 7)
            sinceMemAddr = sinceMemAddr + 1
            timestampAddr = timestampAddr + 1
            ts += toBinary(op[3], 2*timestamp_width) + "\\n"
        # Else, it is not a valid operation.
        elif op[0] == "#":
            line = ""
            for i in range(0,len(op)):
                line = line + op[i] + " "
            print(line)
            continue
        # Else, it is not a valid operation.
        else:
            print("ERROR: line ", i, "(", op, ")")
            continue

        opcode += "\\n"

    return opcode, ts

prog_text = "char *ptm_bin = \""

def assemble_pt(ptasm, ts_ext, gen_dir, no_binaries):
    print('Assembling PT')

    with open(ptasm, 'r') as file:
        f = file.read()

    timestamp_width = 8 * int(ts_ext)
    bin_dir = gen_dir+'binary_files/'
    if(not os.path.isdir(bin_dir)):
        os.mkdir(bin_dir)
    opcode, ts = assemble(f, timestamp_width)

    if no_binaries == 'True':
        global prog_text
        prog_text += opcode + "\";\n"
        prog_text += "char *pti_bin = \"" + ts + "\";\n"
        with open(gen_dir+'config.c', 'a') as c:
            c.write(prog_text)
    else:
        with open(bin_dir+'ptm.bin', 'w') as ptm:
            ptm.write(opcode.replace('\\n','\n'))
        with open(bin_dir+'pti.bin', 'w') as pti:
            pti.write(ts.replace('\\n','\n'))
