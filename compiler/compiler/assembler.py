from ctypes import Structure, Union, c_float, c_int
from typing import Sequence
from .instruction import *

def assemble_bz(filename: str, bzasm: str, opc_width: int, param_width: int) -> None:

    class BZParam(Union):
        _fields_ = [('i',c_int),
                    ('f',c_float)]

    class BZInstruction(Structure):
        _pack_: int = 1
        _fields_ = [('opcode',c_int,opc_width), ('param',BZParam)]

    BZArray = BZInstruction * len(bzasm.splitlines())
    bzarray = BZArray

    i: int = 0
    for line in bzasm.splitlines():
        asm_instr: list(str) = line.split(' ')
        op: str = asm_instr[0]
        param: str

        if op == 'end':
            bzarray[i] = BZInstruction(BZ_NONE, BZParam(0))
        if op == 'store':
            param = BZParam(i=int(asm_instr[1][1:])) # remove preceding 'b'
            bzarray[i] = BZInstruction(BZ_STORE, param)
        elif op == 'iload':
            param = BZParam(i=int(asm_instr[1][1:])) # remove preceding 'b'
            bzarray[i] = BZInstruction(BZ_ILOAD, param)
        elif op == 'fload':
            param = BZParam(i=int(asm_instr[1][1:])) # remove preceding 'b'
            bzarray[i] = BZInstruction(BZ_FLOAD, param)
        elif op == 'iconst':
            param = BZParam(i=int(param))
            bzarray[i] = BZInstruction(BZ_ICONST, param)
        elif op == 'fconst':
            param = BZParam(f=float(asm_instr[1]))
            bzarray[i] = BZInstruction(BZ_FCONST, param)
        # elif op == 'iite':
        #     param = int(asm_instr[1][1:]) # remove preceding 'b'
        #     bin_instr += pack('=ci', BZ_IITE, param)
        # elif op == 'fite':
        #     param = int(asm_instr[1][1:]) # remove preceding 'b'
        #     bin_instr += pack('=cI', BZ_STORE, param)
        elif op == 'bwneg':
            bzarray[i] = BZInstruction(BZ_BWNEG, BZParam(0))
        elif op == 'and':
            bzarray[i] = BZInstruction(BZ_BWAND, BZParam(0))
        elif op == 'or':
            bzarray[i] = BZInstruction(BZ_BWOR, BZParam(0))
        elif op == 'xor':
            bzarray[i] = BZInstruction(BZ_BWXOR, BZParam(0))
        elif op == 'ieq':
            bzarray[i] = BZInstruction(BZ_IEQ, BZParam(0))
        elif op == 'feq':
            param = BZParam(f=float(asm_instr[1]))
            bzarray[i] = BZInstruction(BZ_FEQ, param)
        elif op == 'ineq':
            bzarray[i] = BZInstruction(BZ_INEQ, BZParam(0))
        elif op == 'fneq':
            param = BZParam(f=float(asm_instr[1]))
            bzarray[i] = BZInstruction(BZ_FNEQ, param)
        elif op == 'igt':
            bzarray[i] = BZInstruction(BZ_IGT, BZParam(0))
        elif op == 'fgt':
            bzarray[i] = BZInstruction(BZ_FGT, BZParam(0))
        elif op == 'igte':
            bzarray[i] = BZInstruction(BZ_IGTE, BZParam(0))
        elif op == 'fgte':
            bzarray[i] = BZInstruction(BZ_FGTE, BZParam(0))
        elif op == 'ilt':
            bzarray[i] = BZInstruction(BZ_ILT, BZParam(0))
        elif op == 'flt':
            bzarray[i] = BZInstruction(BZ_FLT, BZParam(0))
        elif op == 'ilte':
            bzarray[i] = BZInstruction(BZ_ILTE, BZParam(0))
        elif op == 'flte':
            bzarray[i] = BZInstruction(BZ_FLTE, BZParam(0))
        # elif op == 'ineg':
        #     bin_instr += BZ_INEG
        # elif op == 'fneg':
        #     bin_instr += BZ_FNEG
        elif op == 'iadd':
            bzarray[i] = BZInstruction(BZ_IADD, BZParam(0))
        elif op == 'fadd':
            bin_instr += BZ_FADD
        elif op == 'isub':
            bzarray[i] = BZInstruction(BZ_ISUB, BZParam(0))
        # elif op == 'fsub':
        #     bin_instr += BZ_FSUB
        # elif op == 'imul':
        #     bin_instr += BZ_IMUL
        # elif op == 'fmul':
        #     bin_instr += BZ_FMUL
        # elif op == 'idiv':
        #     bin_instr += BZ_IDIV
        # elif op == 'fdiv':
        #     bin_instr += BZ_FDIV
        # elif op == 'mod':
        #     bin_instr += BZ_MOD
        # elif op == 'aux1':
        #     bin_instr += BZ_AUX1
        # elif op == 'aux2':
        #     bin_instr += BZ_AUX2
        # elif op == 'aux3':
        #     bin_instr += BZ_AUX3
        # elif op == 'aux4':
        #     bin_instr += BZ_AUX4
        else:
            print('error during assembly: invalid opcode')

    with open(filename, 'wb') as f:
        f.write(bzarray)


# def operand2ba(op: str, width: int) -> bitarray:
#     bin: bitarray = bitarray(endian='little')

#     if op == 'True':
#         bin += bitarray('10')
#         bin += int2ba(1, length=width, endian='little')
#     elif op == 'False':
#         bin += bitarray('10')
#         bin += int2ba(0, length=width, endian='little')
#     else: # op is node or atomic
#         optype: str = op[0]
#         opidx: int = int(op[1:])
#         if optype == 'n' or optype == 'f':
#             bin += bitarray('10')
#             bin += int2ba(opidx, length=width, endian='little') # TODO: add check for sufficient width
#         elif optype == 'b':
#             bin += bitarray('00')
#             bin += int2ba(opidx, length=width, endian='little') # TODO: add check for sufficient width

#     return bin


# def assemble_ft(ftasm: str, opc_width: int, opnd_width: int, ts_width: int, scr_width: int) -> bitarray:
    # class TLInstruction(Structure):
    #     _fields_: Sequence[tuple[str, type[_CData], int]] = \
    #         [('opcode',c_int,5),
    #         ('op1',c_int,10),
    #         ('op2',c_int,10),
    #         ('intvl_addr',c_int,8),
    #         ('scratch',c_int,7)]
#     bin: bitarray = bitarray(endian='little')
#     intvl_bin: bitarray = bitarray(endian='little')
    
#     num_intvls: int = 0
#     ts_addr: int = 0
#     unary_mem_addr: int = 0
#     binary_mem_addr: int = 0

#     instr_width: int = opc_width + 2*(opnd_width+2) + ts_width + scr_width
#     instr_width = instr_width + (instr_width % 8)

#     intvl_width: int = 2 * ts_width
#     intvl_width = intvl_width + (intvl_width % 8)

#     # start w number of instructions
#     # bin += int2ba(int(len(ftasm.splitlines())),length=32)

#     for line in ftasm.splitlines():
#         asm_instr: list[str] = line.split(' ')
#         bin_instr: bitarray = bitarray(endian='little')

#         op: str = asm_instr[1]

#         if op == 'load':
#             bin_instr += TL_FT_LOAD
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'end':
#             bin_instr += TL_END
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += operand2ba(asm_instr[3],opnd_width)
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'endsequence':
#             bin_instr += TL_END_SEQ
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'not':
#             bin_instr += TL_FT_NOT
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'and':
#             bin_instr += TL_FT_AND
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += operand2ba(asm_instr[3],opnd_width)
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'or':
#             bin_instr += TL_OR
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += operand2ba(asm_instr[3],opnd_width)
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'impl':
#             bin_instr += TL_FT_IMPL
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += operand2ba(asm_instr[3],opnd_width)
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'equiv':
#             bin_instr += TL_EQUIV
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += operand2ba(asm_instr[3],opnd_width)
#             bin_instr += zeros(instr_width-len(bin_instr))
#         elif op == 'global':
#             bin_instr += TL_FT_GLOBAL
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += zeros(opnd_width+2)
#             bin_instr += int2ba(ts_addr, length=ts_width, endian='little')
#             bin_instr += int2ba(unary_mem_addr, length=scr_width, endian='little')
#             bin_instr += zeros(instr_width-len(bin_instr))

#             lb: int = int(asm_instr[3])
#             ub: int = int(asm_instr[4])
#             intvl_bin += int2ba(lb, length=ts_width, endian='little')
#             intvl_bin += int2ba(ub, length=ts_width, endian='little')

#             ts_addr += 1
#             unary_mem_addr += 1
#         elif op == 'future':
#             bin_instr += TL_FT_FUTURE
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += zeros(opnd_width+2)
#             bin_instr += int2ba(ts_addr, length=ts_width, endian='little')
#             bin_instr += int2ba(unary_mem_addr, length=scr_width, endian='little')
#             bin_instr += zeros(instr_width-len(bin_instr))

#             lb: int = int(asm_instr[3])
#             ub: int = int(asm_instr[4])
#             intvl_bin += int2ba(lb, length=ts_width, endian='little')
#             intvl_bin += int2ba(ub, length=ts_width, endian='little')

#             ts_addr += 1
#             unary_mem_addr += 1
#         elif op == 'until':
#             bin_instr += TL_FT_UNTIL
#             bin_instr += operand2ba(asm_instr[2],opnd_width)
#             bin_instr += operand2ba(asm_instr[3],opnd_width)
#             bin_instr += int2ba(ts_addr, length=ts_width, endian='little')
#             bin_instr += int2ba(binary_mem_addr, length=scr_width, endian='little')
#             bin_instr += zeros(instr_width-len(bin_instr))

#             lb: int = int(asm_instr[4])
#             ub: int = int(asm_instr[5])
#             intvl_bin += int2ba(lb, length=ts_width, endian='little')
#             intvl_bin += int2ba(ub, length=ts_width, endian='little')

#             ts_addr += 1
#             binary_mem_addr += 1
#         else:
#             print('error during assembly: invalid opcode')

#         assert len(bin_instr) == instr_width

#         bin += bin_instr

#     # pad with zeroes to align bytes
#     bin += zeros(len(bin) % 8)

#     # start intervals w number of intervals
#     bin += int2ba(num_intvls,length=32, endian='little')
#     bin += intvl_bin

#     # pad with zeroes to align bytes
#     bin += zeros(len(bin) % 8)

#     return bin


# def assemble_pt(ptasm: str, opc_width: int, opnd_width: int, ts_width: int, scr_width: int) -> bitarray:
#     bin: bitarray = bitarray(endian='little')

#     for line in ptasm.splitlines():
#         pass

#     return bin


# def assemble_ftscq(ftscqasm: str, scq_addr_width: int) -> bitarray:
    # class SCQ(Structure):
    #     _fields_: Sequence[tuple[str, type[_CData], int]] = \
    #         [('start',c_int,16),
    #         ('end',c_int,16)]

#     bin: bitarray = bitarray(endian='little')

#     # start w number of SCQs
#     bin += int2ba(len(ftscqasm.splitlines()), length=32, endian='little')

#     for line in ftscqasm.splitlines():
#         pos = line.split(' ')
#         st_pos = int(pos[0])
#         end_pos = int(pos[1])
#         bin += int2ba(st_pos, length=scq_addr_width, endian='little')
#         bin += int2ba(end_pos, length=scq_addr_width, endian='little')

#     # pad with zeroes to align bytes
#     bin += zeros(len(bin) % 8)

#     return bin


def assemble(filename: str, bzasm: str, ftasm: str, ptasm: str, ftscqasm: str):
    with open(filename,'wb') as f:
        f.write(b'\x00')

    assemble_bz(filename,bzasm,8,32)

    with open(filename,'rb') as f:
        f.read()