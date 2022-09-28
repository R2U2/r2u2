from bitarray import bitarray
from bitarray.util import int2ba

def assemble_bz(bzasm: str) -> bytearray:
    bin: bitarray = bitarray()

    # start BZ with number of instructions
    bin += int2ba(int(len(bzasm.splitlines())),length=32)

    print(bin)

    for line in bzasm.splitlines():
        instr: str = line.split(' ')

        op: str = instr[0]
        param: str

        if op == 'store':
            param = instr[1][1:]
            bin.extend('000001')
            bin.frombytes(b'%(param)i' % {b'param': int(param)})
        elif op == 'iload':
            param = instr[1][1:]
            bin.extend('000010')
            bin.frombytes(b'%(param)i' % {b'param': int(param)})
        elif op == 'fload':
            param = instr[1][1:]
            bin.extend('000011')
            bin.frombytes(b'%(param)i' % {b'param': int(param)})
        elif op == 'iconst':
            param = instr[1]
            bin.extend('000100')
            bin.frombytes(b'%(param)i' % {b'param': int(param)})
        elif op == 'fconst':
            param = instr[1][1:]
            bin.extend('000101')
            bin.frombytes(b'%(param)f' % {b'param': float(param)})
        elif op == 'iite':
            param = instr[1][1:]
            bin.extend('000110')
            bin.frombytes(b'%(param)i' % {b'param': int(param)})
        elif op == 'fite':
            param = instr[1][1:]
            bin.extend('000111')
            bin.frombytes(b'%(param)i' % {b'param': int(param)})
        elif op == 'bneg':
            bin.extend('001000')
        elif op == 'and':
            bin.extend('001001')
        elif op == 'or':
            bin.extend('001010')
        elif op == 'xor':
            bin.extend('001011')
        elif op == 'ieq':
            bin.extend('001100')
        elif op == 'feq':
            param = instr[1][1:]
            bin.extend('001101')
            bin.frombytes(b'%(param)f' % {b'param': float(param)})
        elif op == 'ineq':
            bin.extend('001110')
        elif op == 'fneq':
            param = instr[1][1:]
            bin.extend('001111')
            bin.frombytes(b'%(param)f' % {b'param': float(param)})
        elif op == 'igt':
            bin.extend('010000')
        elif op == 'fgt':
            bin.extend('010001')
        elif op == 'igte':
            bin.extend('010010')
        elif op == 'fgte':
            bin.extend('010011')
        elif op == 'ilt':
            bin.extend('010100')
        elif op == 'flt':
            bin.extend('010101')
        elif op == 'ilte':
            bin.extend('010110')
        elif op == 'flte':
            bin.extend('010111')
        elif op == 'ianeg':
            bin.extend('011000')
        elif op == 'faneg':
            bin.extend('011001')
        elif op == 'iadd':
            bin.extend('011010')
        elif op == 'fadd':
            bin.extend('011011')
        elif op == 'isub':
            bin.extend('011100')
        elif op == 'fsub':
            bin.extend('011101')
        elif op == 'imul':
            bin.extend('011110')
        elif op == 'fmul':
            bin.extend('011111')
        elif op == 'idiv':
            bin.extend('100000')
        elif op == 'fdiv':
            bin.extend('100001')
        elif op == 'mod':
            bin.extend('100010')
        else:
            print('error during assembly: invalid opcode')

    return bin


def assemble_ft(ftasm: str) -> bytes:
    bin: bytes = b''

    for line in ftasm.splitlines():
        pass

    return b''


def assemble_pt(ptasm: str) -> bytes:
    bin: bytes = b''

    for line in ptasm.splitlines():
        pass

    return b''


def assemble_ftscq(ftscqasm: str) -> bytes:
    bin: bytes = b''

    for line in ftscqasm.splitlines():
        pass

    return b''


def assemble(filename: str, bzasm: str, ftasm: str, ptasm: str, ftscqasm: str):
    bin: bytes = b''

    bin += assemble_bz(bzasm)
    bin += assemble_ft(ftasm)
    bin += assemble_pt(ptasm)
    bin += assemble_ftscq(ftscqasm)

    with open(filename,'wb') as f:
        f.write(bin)