from struct import pack
from bitarray import bitarray
from array import array

### BZ Opcodes
BZ_NONE:   bytes = b'\x00'
BZ_STORE:  bytes = b'\x01'
BZ_ILOAD:  bytes = b'\x02'
BZ_FLOAD:  bytes = b'\x03'
BZ_ICONST: bytes = b'\x04'
BZ_FCONST: bytes = b'\x05'
BZ_IITE:   bytes = b'\x06'
BZ_FITE:   bytes = b'\x07'
BZ_BWNEG:  bytes = b'\x08'
BZ_BWAND:  bytes = b'\x09'
BZ_BWOR:   bytes = b'\x0A'
BZ_BWXOR:  bytes = b'\x0B'
BZ_IEQ:    bytes = b'\x0C'
BZ_FEQ:    bytes = b'\x0D'
BZ_INEQ:   bytes = b'\x0E'
BZ_FNEQ:   bytes = b'\x0F'
BZ_IGT:    bytes = b'\x10'
BZ_FGT:    bytes = b'\x12'
BZ_IGTE:   bytes = b'\x13'
BZ_FGTE:   bytes = b'\x14'
BZ_ILT:    bytes = b'\x15'
BZ_FLT:    bytes = b'\x16'
BZ_ILTE:   bytes = b'\x17'
BZ_FLTE:   bytes = b'\x18'
BZ_INEG:   bytes = b'\x19'
BZ_FNEG:   bytes = b'\x1A'
BZ_IADD:   bytes = b'\x1B'
BZ_FADD:   bytes = b'\x1C'
BZ_ISUB:   bytes = b'\x1D'
BZ_FSUB:   bytes = b'\x1E'
BZ_IMUL:   bytes = b'\x1F'
BZ_FMUL:   bytes = b'\x20'
BZ_IDIV:   bytes = b'\x21'
BZ_FDIV:   bytes = b'\x22'
BZ_MOD:    bytes = b'\x23'
BZ_AUX1:   bytes = b'\x24'
BZ_AUX2:   bytes = b'\x25'
BZ_AUX3:   bytes = b'\x26'
BZ_AUX4:   bytes = b'\x27'

### TL Opcodes
TL_START:     bytes = b''
TL_END:       bytes = b''
TL_END_SEQ:   bytes = b''
TL_NOP:       bytes = b''
TL_NOT:       bytes = b''
TL_AND:       bytes = b''
TL_OR:        bytes = b''
TL_EQUIV:     bytes = b''
TL_IMPL:      bytes = b''
TL_FT_NOT:    bytes = b''
TL_FT_AND:    bytes = b''
TL_FT_IMPL:   bytes = b''
TL_FT_GLOBAL: bytes = b''
TL_FT_FUTURE: bytes = b''
TL_FT_UNTIL:  bytes = b''
TL_FT_LOAD:   bytes = b''
TL_PT_YSTRDY: bytes = b''
TL_PT_ONCE:   bytes = b''
TL_PT_HIST:   bytes = b''
TL_PT_SINCE:  bytes = b''

### Unused TL Opcodes
TL_FT_GLOBAL_TP: bytes = b''
TL_FT_FUTURE_TP: bytes = b''
TL_PT_ONCE_TP:   bytes = b''
TL_PT_HIST_TP:   bytes = b''
TL_PT_SINCE_TP:  bytes = b''


def assemble_bz(bzasm: str, opc_width: int, param_width: int) -> bytearray:
    bin: bytearray = bytearray()

    num_params: int = 0
    num_instr: int = 0

    for line in bzasm.splitlines():
        asm_instr: list[str] = line.split(' ')
        bin_instr: bytearray = bytearray()

        op: str = asm_instr[0]
        param: str

        if op == 'end':
            bin_instr += BZ_NONE
        if op == 'store':
            param = int(asm_instr[1][1:]) # remove preceding 'b'
            bin_instr += pack('=cI', BZ_STORE, param)
            num_params += 1
        elif op == 'iload':
            param = int(asm_instr[1][1:]) # remove preceding 's'
            bin_instr += pack('=cI', BZ_ILOAD, param)
            num_params += 1
        elif op == 'fload':
            param = int(asm_instr[1][1:]) # remove preceding 's'
            bin_instr += pack('=cI', BZ_FLOAD, param)
            num_params += 1
        elif op == 'iconst':
            param = int(param)
            bin_instr += pack('=ci', BZ_ICONST, param)
            num_params += 1
        elif op == 'fconst':
            param = float(asm_instr[1])
            bin_instr += pack('=cf', BZ_FCONST, param)
            num_params += 1
        # elif op == 'iite':
        #     param = int(asm_instr[1][1:]) # remove preceding 'b'
        #     bin_instr += pack('=ci', BZ_IITE, param)
        # elif op == 'fite':
        #     param = int(asm_instr[1][1:]) # remove preceding 'b'
        #     bin_instr += pack('=cI', BZ_STORE, param)
        elif op == 'bwneg':
            bin_instr += BZ_BWNEG
        elif op == 'and':
            bin_instr += BZ_BWAND
        elif op == 'or':
            bin_instr += BZ_BWOR
        elif op == 'xor':
            bin_instr += BZ_BWXOR
        elif op == 'ieq':
            bin_instr += BZ_IEQ
        elif op == 'feq':
            param = float(asm_instr[1])
            bin_instr += pack('=cf', BZ_FEQ, param)
            num_params += 1
        elif op == 'ineq':
            bin_instr += BZ_INEQ
        elif op == 'fneq':
            param = float(asm_instr[1])
            bin_instr += pack('=cf', BZ_FNEQ, param)
            num_params += 1
        elif op == 'igt':
            bin_instr += BZ_IGT
        elif op == 'fgt':
            bin_instr += BZ_FGT
        elif op == 'igte':
            bin_instr += BZ_IGTE
        elif op == 'fgte':
            bin_instr += BZ_FGTE
        elif op == 'ilt':
            bin_instr += BZ_ILT
        elif op == 'flt':
            bin_instr += BZ_FLT
        elif op == 'ilte':
            bin_instr += BZ_ILTE
        elif op == 'flte':
            bin_instr += BZ_FLTE
        elif op == 'ineg':
            bin_instr += BZ_INEG
        elif op == 'fneg':
            bin_instr += BZ_FNEG
        elif op == 'iadd':
            bin_instr += BZ_IADD
        elif op == 'fadd':
            bin_instr += BZ_FADD
        elif op == 'isub':
            bin_instr += BZ_ISUB
        elif op == 'fsub':
            bin_instr += BZ_FSUB
        elif op == 'imul':
            bin_instr += BZ_IMUL
        elif op == 'fmul':
            bin_instr += BZ_FMUL
        elif op == 'idiv':
            bin_instr += BZ_IDIV
        elif op == 'fdiv':
            bin_instr += BZ_FDIV
        elif op == 'mod':
            bin_instr += BZ_MOD
        elif op == 'aux1':
            bin_instr += BZ_AUX1
        elif op == 'aux2':
            bin_instr += BZ_AUX2
        elif op == 'aux3':
            bin_instr += BZ_AUX3
        elif op == 'aux4':
            bin_instr += BZ_AUX4
        else:
            print('error during assembly: invalid opcode')

        num_instr += 1
        bin += bin_instr

    bin += pack('=c',BZ_NONE)
    bin = pack('=Q',num_instr+4*num_params) + bin

    return bin


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
    bin: bytearray = bytearray()

    bin += assemble_bz(bzasm,1,4)
    # bin += assemble_ft(ftasm,5,8,8,7)
    # bin += assemble_pt(ptasm,5,8,8,7)
    # bin += assemble_ftscq(ftscqasm,16)

    # b: bitarray = int2ba(8,length=32)
    # b = make_endian(b,'big')
    # b = b + make_endian(bin,'big')

    # print(ba2hex(b))

    with open(filename,'wb') as f:
        f.write(bin)