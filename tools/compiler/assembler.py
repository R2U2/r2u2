from bitarray import bitarray
from bitarray.util import int2ba, zeros, make_endian, ba2hex
from array import array

### BZ Opcodes
BZ_NONE:   bitarray = bitarray('000000')
BZ_STORE:  bitarray = bitarray('000001')
BZ_ILOAD:  bitarray = bitarray('000010')
BZ_FLOAD:  bitarray = bitarray('000011')
BZ_ICONST: bitarray = bitarray('000100')
BZ_FCONST: bitarray = bitarray('000101')
BZ_IITE:   bitarray = bitarray('000110')
BZ_FITE:   bitarray = bitarray('000111')
BZ_BWNEG:  bitarray = bitarray('001000')
BZ_BWAND:  bitarray = bitarray('001001')
BZ_BWOR:   bitarray = bitarray('001010')
BZ_BWXOR:  bitarray = bitarray('001011')
BZ_IEQ:    bitarray = bitarray('001100')
BZ_FEQ:    bitarray = bitarray('001101')
BZ_INEQ:   bitarray = bitarray('001110')
BZ_FNEQ:   bitarray = bitarray('001111')
BZ_IGT:    bitarray = bitarray('010000')
BZ_FGT:    bitarray = bitarray('010001')
BZ_IGTE:   bitarray = bitarray('010010')
BZ_FGTE:   bitarray = bitarray('010011')
BZ_ILT:    bitarray = bitarray('010100')
BZ_FLT:    bitarray = bitarray('010101')
BZ_ILTE:   bitarray = bitarray('010110')
BZ_FLTE:   bitarray = bitarray('010111')
BZ_INEG:   bitarray = bitarray('011000')
BZ_FNEG:   bitarray = bitarray('011001')
BZ_IADD:   bitarray = bitarray('011010')
BZ_FADD:   bitarray = bitarray('011011')
BZ_ISUB:   bitarray = bitarray('011100')
BZ_FSUB:   bitarray = bitarray('011101')
BZ_IMUL:   bitarray = bitarray('011110')
BZ_FMUL:   bitarray = bitarray('011111')
BZ_IDIV:   bitarray = bitarray('100000')
BZ_FDIV:   bitarray = bitarray('100001')
BZ_MOD:    bitarray = bitarray('100010')
BZ_AUX1:   bitarray = bitarray('100011')
BZ_AUX2:   bitarray = bitarray('100100')
BZ_AUX3:   bitarray = bitarray('100101')
BZ_AUX4:   bitarray = bitarray('100110')

### TL Opcodes
TL_START:     bitarray = bitarray('01011')
TL_END:       bitarray = bitarray('01100')
TL_END_SEQ:   bitarray = bitarray('11111')
TL_NOP:       bitarray = bitarray('11110')
TL_NOT:       bitarray = bitarray('00011')
TL_AND:       bitarray = bitarray('00100')
TL_OR:        bitarray = bitarray('00101')
TL_EQUIV:     bitarray = bitarray('00111')
TL_IMPL:      bitarray = bitarray('00110')
TL_FT_NOT:    bitarray = bitarray('10100')
TL_FT_AND:    bitarray = bitarray('10101')
TL_FT_IMPL:   bitarray = bitarray('11011')
TL_FT_GLOBAL: bitarray = bitarray('10111')
TL_FT_FUTURE: bitarray = bitarray('11001')
TL_FT_UNTIL:  bitarray = bitarray('11010')
TL_FT_LOAD:   bitarray = bitarray('11100')
TL_PT_YSTRDY: bitarray = bitarray('01000')
TL_PT_ONCE:   bitarray = bitarray('10000')
TL_PT_HIST:   bitarray = bitarray('10010')
TL_PT_SINCE:  bitarray = bitarray('10011')

### Unused TL Opcodes
TL_FT_GLOBAL_TP: bitarray = bitarray('10110')
TL_FT_FUTURE_TP: bitarray = bitarray('11000')
TL_PT_ONCE_TP:   bitarray = bitarray('01001')
TL_PT_HIST_TP:   bitarray = bitarray('01010')
TL_PT_SINCE_TP:  bitarray = bitarray('01110')



def assemble_bz(bzasm: str, opc_width: int, param_width: int) -> bytearray:
    bin: bitarray = bitarray()

    # start BZ with number of instructions
    bin += int2ba(int(len(bzasm.splitlines())),length=32)

    print(len(bzasm.splitlines()))
    print(ba2hex(bin))

    for line in bzasm.splitlines():
        asm_instr: list[str] = line.split(' ')
        bin_instr: bitarray = bitarray()

        op: str = asm_instr[0]
        param: str

        if op == 'store':
            param = int(asm_instr[1][1:]) # remove preceding 'b'
            bin_instr += BZ_STORE
            bin_instr += int2ba(param,length=param_width)
        elif op == 'iload':
            param = int(asm_instr[1][1:]) # remove preceding 's'
            bin_instr += BZ_ILOAD
            bin_instr += int2ba(param,length=param_width)
        elif op == 'fload':
            param = int(asm_instr[1][1:]) # remove preceding 's'
            bin_instr += BZ_FLOAD
            bin_instr += int2ba(param,length=param_width)
        elif op == 'iconst':
            param = int(param)
            bin_instr += BZ_ICONST
            bin_instr += int2ba(param,length=param_width)
        elif op == 'fconst':
            param = float(asm_instr[1])
            bin_instr += BZ_FCONST
            bin_instr.frombytes(array('f',[param]).tobytes())
        elif op == 'iite':
            param = int(asm_instr[1][1:]) # remove preceding 'b'
            bin_instr += BZ_IITE
            bin_instr += int2ba(param,length=param_width)
        elif op == 'fite':
            param = int(asm_instr[1][1:]) # remove preceding 'b'
            bin_instr += BZ_FITE
            bin_instr += int2ba(param,length=param_width)
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
            bin_instr += BZ_FEQ
            bin.frombytes(array('f',[param]).tobytes())
        elif op == 'ineq':
            bin_instr += BZ_INEQ
        elif op == 'fneq':
            param = float(asm_instr[1])
            bin_instr += BZ_FNEQ
            bin_instr.frombytes(array('f',[param]).tobytes())
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

        bin += bin_instr

    # pad with zeroes to align bytes
    bin += zeros(len(bin) % 8)

    return bin


def operand2ba(op: str, width: int) -> bitarray:
    bin: bitarray = bitarray()

    if op == 'True':
        bin += bitarray('10')
        bin += int2ba(1,length=width)
    elif op == 'False':
        bin += bitarray('10')
        bin += int2ba(0,length=width)
    else: # op is node or atomic
        optype: str = op[0]
        opidx: int = int(op[1:])
        if optype == 'n' or optype == 'f':
            bin += bitarray('10')
            bin += int2ba(opidx,length=width) # TODO: add check for sufficient width
        elif optype == 'b':
            bin += bitarray('00')
            bin += int2ba(opidx,length=width) # TODO: add check for sufficient width

    return bin


def assemble_ft(ftasm: str, opc_width: int, opnd_width: int, ts_width: int, scr_width: int) -> bitarray:
    bin: bitarray = bitarray()
    intvl_bin: bitarray = bitarray()
    
    num_intvls: int = 0
    ts_addr: int = 0
    unary_mem_addr: int = 0
    binary_mem_addr: int = 0
    instr_width: int = opc_width + 2*(opnd_width+2) + ts_width + scr_width

    # start w number of instructions
    # bin += int2ba(int(len(ftasm.splitlines())),length=32)

    for line in ftasm.splitlines():
        asm_instr: list[str] = line.split(' ')
        bin_instr: bitarray = bitarray()

        op: str = asm_instr[1]

        if op == 'load':
            bin_instr += TL_FT_LOAD
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += zeros(instr_width-opc_width-(opnd_width+2))
        elif op == 'end':
            bin_instr += TL_END
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += operand2ba(asm_instr[3],opnd_width)
            bin_instr += zeros(instr_width-opc_width-2*(opnd_width+2))
        elif op == 'endsequence':
            bin_instr += TL_END_SEQ
            bin_instr += zeros(instr_width-opc_width)
        elif op == 'not':
            bin_instr += TL_FT_NOT
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += zeros(instr_width-opc_width-(opnd_width+2))
        elif op == 'and':
            bin_instr += TL_FT_AND
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += operand2ba(asm_instr[3],opnd_width)
            bin_instr += zeros(instr_width-opc_width-2*(opnd_width+2))
        elif op == 'or':
            bin_instr += TL_OR
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += operand2ba(asm_instr[3],opnd_width)
            bin_instr += zeros(instr_width-opc_width-2*(opnd_width+2))
        elif op == 'impl':
            bin_instr += TL_FT_IMPL
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += operand2ba(asm_instr[3],opnd_width)
            bin_instr += zeros(instr_width-opc_width-2*(opnd_width+2))
        elif op == 'equiv':
            bin_instr += TL_EQUIV
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += operand2ba(asm_instr[3],opnd_width)
            bin_instr += zeros(instr_width-opc_width-2*(opnd_width+2))
        elif op == 'global':
            bin_instr += TL_FT_GLOBAL
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += zeros(opnd_width+2)
            bin_instr += int2ba(ts_addr, length=ts_width)
            bin_instr += int2ba(unary_mem_addr, length=scr_width)

            lb: int = int(asm_instr[3])
            ub: int = int(asm_instr[4])
            intvl_bin += int2ba(lb, length=ts_width)
            intvl_bin += int2ba(ub, length=ts_width)

            ts_addr += 1
            unary_mem_addr += 1
        elif op == 'future':
            bin_instr += TL_FT_FUTURE
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += zeros(opnd_width+2)
            bin_instr += int2ba(ts_addr, length=ts_width)
            bin_instr += int2ba(unary_mem_addr, length=scr_width)

            lb: int = int(asm_instr[3])
            ub: int = int(asm_instr[4])
            intvl_bin += int2ba(lb, length=ts_width)
            intvl_bin += int2ba(ub, length=ts_width)

            ts_addr += 1
            unary_mem_addr += 1
        elif op == 'until':
            bin_instr += TL_FT_UNTIL
            bin_instr += operand2ba(asm_instr[2],opnd_width)
            bin_instr += operand2ba(asm_instr[3],opnd_width)
            bin_instr += int2ba(ts_addr, length=ts_width)
            bin_instr += int2ba(binary_mem_addr, length=scr_width)

            lb: int = int(asm_instr[4])
            ub: int = int(asm_instr[5])
            intvl_bin += int2ba(lb, length=ts_width)
            intvl_bin += int2ba(ub, length=ts_width)

            ts_addr += 1
            binary_mem_addr += 1
        else:
            print('error during assembly: invalid opcode')

        assert len(bin_instr) == instr_width

        bin += bin_instr

    # pad with zeroes to align bytes
    bin += zeros(len(bin) % 8)

    # start intervals w number of intervals
    bin += int2ba(num_intvls,length=32)
    bin += intvl_bin

    # pad with zeroes to align bytes
    bin += zeros(len(bin) % 8)

    return bin


def assemble_pt(ptasm: str, opc_width: int, opnd_width: int, ts_width: int, scr_width: int) -> bitarray:
    bin: bitarray = bitarray()

    for line in ptasm.splitlines():
        pass

    return bin


def assemble_ftscq(ftscqasm: str, scq_addr_width: int) -> bitarray:
    bin: bitarray = bitarray()

    # start w number of SCQs
    bin += int2ba(len(ftscqasm.splitlines()), length=32)

    for line in ftscqasm.splitlines():
        pos = line.split(' ')
        st_pos = int(pos[0])
        end_pos = int(pos[1])
        bin += int2ba(st_pos, length=scq_addr_width)
        bin += int2ba(end_pos, length=scq_addr_width)

    # pad with zeroes to align bytes
    bin += zeros(len(bin) % 8)

    return bin


def assemble(filename: str, bzasm: str, ftasm: str, ptasm: str, ftscqasm: str):
    bin: bitarray = bitarray()

    bin += assemble_bz(bzasm,6,32)
    bin += assemble_ft(ftasm,5,8,8,8)
    bin += assemble_pt(ptasm,5,8,8,8)
    bin += assemble_ftscq(ftscqasm,16)

    make_endian(bin,'little')

    with open(filename,'wb') as f:
        f.write(bin)