from __future__ import annotations
from typing import Sequence, Dict, List, Tuple
from ctypes import Structure, Union, c_float, c_int
from enum import Enum
from struct import Struct as cStruct
from .ast import *

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

class ENGINE_TAGS(Enum):
    NA = 0 # Null instruction tag - acts as ENDSEQ
    SY = 1 # System commands - reserved for monitor control
    CG = 2 # Immediate Configuration Directive
    AT = 3 # Original Atomic Checker
    TL = 4 # MLTL Temporal logic engine
    BZ = 5 # Booleanizer

class AT_COND(Enum):
    EQ  = 0b000
    NEQ = 0b001
    LT  = 0b010
    LEQ = 0b011
    GT  = 0b100
    GEQ = 0b101

class AT_FILTER(Enum):
    BOOL           = 0b0001
    INT            = 0b0010
    FLOAT          = 0b0011
    #if R2U2_AT_Extra_Filters
    RATE           = 0b0100
    ABS_DIFF_ANGLE = 0b0101
    MOVAVG         = 0b0110
    #endif
    #if R2U2_AT_Signal_Sets
    EXACTLY_ONE_OF = 0b0111
    NONE_OF        = 0b1000
    ALL_OF         = 0b1001
    #endif

def assemble_at(conditional, filter, sig_addr, atom_addr, comp_is_sig, comparison):
    at_instruction = cStruct('iiBBBxxxxx8sd')
    return at_instruction.pack(conditional.value, filter.value, sig_addr, atom_addr, comp_is_sig, comparison, 0.00001)

class TL_OPERAND_TYPES(Enum):
    DIRECT      = 0b01
    ATOMIC      = 0b00
    SUBFORMULA  = 0b10
    NOT_SET     = 0b11

class FT_OP_CODES(Enum):
    NOP       = 0b11111
    CONFIGURE = 0b11110
    LOAD      = 0b11101
    RETURN    = 0b11100
    GLOBALLY  = 0b11010
    UNTIL     = 0b11001
    NOT       = 0b10111
    AND       = 0b10110


def assemble_ft(opcode, operand_1, operand_2, ref):
    # print(f"{FT_OP_CODES(opcode)} ({TL_OPERAND_TYPES(operand_1[0])}, {operand_1[1]}) ({TL_OPERAND_TYPES(operand_2[0])}, {operand_2[1]}), {ref}")

    # The module memoizes these by their description string so this isn't as
    # wasteful as it initially appears
    operand = cStruct('iBxxx')
    ft_instruction = cStruct(f"i{operand.size}s{operand.size}sN")
    return ft_instruction.pack(opcode.value,
                        operand.pack(operand_1[0].value,operand_1[1]),
                        operand.pack(operand_2[0].value,operand_2[1]),
                        ref)

class PT_OP_CODES(Enum):
    NOP          = 0b01111
    CONFIGURE    = 0b01110
    LOAD         = 0b01101
    RETURN       = 0b01100
    ONCE         = 0b01011
    HISTORICALLY = 0b01010
    SINCE        = 0b01001
    NOT          = 0b00111
    AND          = 0b00110
    OR           = 0b00101
    IMPLIES      = 0b00100
    EQUIVALENT   = 0b00000

def assemble_pt(opcode, operand_1, operand_2, ref) -> None:
    # print(f"{PT_OP_CODES(opcode)} ({TL_OPERAND_TYPES(operand_1[0])}, {operand_1[1]}) ({TL_OPERAND_TYPES(operand_2[0])}, {operand_2[1]}), {ref}")

    # The module memoizes these by their description string so this isn't as
    # wasteful as it initially appears
    operand = cStruct('iBxxx')
    ft_instruction = cStruct(f"i{operand.size}s{operand.size}sN")
    return ft_instruction.pack(opcode.value,
                        operand.pack(operand_1[0].value,operand_1[1]),
                        operand.pack(operand_2[0].value,operand_2[1]),
                        ref)
    pass

def assemble_alias() -> None:
    pass

def assemble(filename: List[Instruction], atasm: List[Instruction], bzasm: List[Instruction], ftasm: List[Instruction], ftscqasm: List[Tuple[int,int]], ptasm: List[Instruction],  aliases: List[str]):

    # Concatenate runtime instructions, assume V2 ordering
    # foo: List[Instruction] = atasm + bzasm + ftasm + ptasm

    # Create a list of runtime instrucitons and config instructions
    rtm_instrs: List[bytes] = []
    cfg_instrs: List[bytes] = []

    for instr in atasm:

        if isinstance(instr.rel_op, Equal):
            conditional = AT_COND.EQ
        elif isinstance(instr.rel_op, NotEqual):
            conditional = AT_COND.NEQ
        elif isinstance(instr.rel_op, GreaterThan):
            conditional = AT_COND.GT
        elif isinstance(instr.rel_op, LessThan):
            conditional = AT_COND.LT
        elif isinstance(instr.rel_op, GreaterThanOrEqual):
            conditional = AT_COND.GEQ
        elif isinstance(instr.rel_op, LessThanOrEqual):
            conditional = AT_COND.LEQ

        if instr.filter == "bool":
            filter = AT_FILTER.BOOL
            format = "?xxxxxxx"
        elif instr.filter == "int":
            filter = AT_FILTER.INT
            format = "q"
        elif instr.filter == "float":
            filter = AT_FILTER.FLOAT
            format = "d"

        comp_to_sig = isinstance(instr.compare, Signal)
        if comp_to_sig:
            argument = cStruct("Bxxxxxxx").pack(instr.compare.sid)
        else:
            argument = cStruct(format).pack(instr.compare.value)

        rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.AT.value) + assemble_at(conditional, filter, instr.args[0].sid, instr.atid, comp_to_sig, argument))

    for instr in ftasm:
        if isinstance(instr, Atomic):  # Load
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.LOAD, (TL_OPERAND_TYPES.ATOMIC, instr.atid), (TL_OPERAND_TYPES.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Specification):  # End
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.RETURN, (TL_OPERAND_TYPES.SUBFORMULA, instr.get_expr().tlid), (TL_OPERAND_TYPES.DIRECT, instr.formula_number), instr.tlid))
        elif isinstance(instr, Global): # Globally
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.GLOBALLY, (TL_OPERAND_TYPES.SUBFORMULA, instr.get_children()[0].tlid), (TL_OPERAND_TYPES.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Until):  # Until
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.UNTIL, op1, op2, instr.tlid))
            pass
        elif isinstance(instr, LogicalNegate):  # Not
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.NOT, op1, (TL_OPERAND_TYPES.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, LogicalAnd): # And
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.AND, op1, op2, instr.tlid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplmentedError

        # Configure SCQ size and, if temporal, interval bounds
        cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.CONFIGURE, (TL_OPERAND_TYPES.SUBFORMULA, instr.tlid), (TL_OPERAND_TYPES.DIRECT, ftscqasm[instr.tlid][1] - ftscqasm[instr.tlid][0]), ftscqasm[instr.tlid][0]))
        if isinstance(instr, TemporalOperator):
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.CONFIGURE, (TL_OPERAND_TYPES.SUBFORMULA, instr.tlid), (TL_OPERAND_TYPES.ATOMIC, 0), instr.interval.lb))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.CONFIGURE, (TL_OPERAND_TYPES.SUBFORMULA, instr.tlid), (TL_OPERAND_TYPES.ATOMIC, 1), instr.interval.ub))

    boxqs = 1 # Number of boxqueus for running offsets
    for instr in ptasm:
        if isinstance(instr, Atomic):  # Load
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.LOAD, (TL_OPERAND_TYPES.ATOMIC, instr.atid), (TL_OPERAND_TYPES.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Specification):  # End
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.RETURN, (TL_OPERAND_TYPES.SUBFORMULA, instr.get_expr().tlid), (TL_OPERAND_TYPES.DIRECT, instr.formula_number), instr.tlid))
        elif isinstance(instr, Once): # Once
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.ONCE, (TL_OPERAND_TYPES.SUBFORMULA, instr.get_children()[0].tlid), (TL_OPERAND_TYPES.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Historical): # Historically
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.HISTORICALLY, (TL_OPERAND_TYPES.SUBFORMULA, instr.get_children()[0].tlid), (TL_OPERAND_TYPES.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Since):  # Since
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.SINCE, op1, op2, instr.tlid))
            pass
        elif isinstance(instr, LogicalNegate):  # Not
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.NOT, op1, (TL_OPERAND_TYPES.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, LogicalAnd): # And
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplmentedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.AND, op1, op2, instr.tlid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplmentedError

        if isinstance(instr, TemporalOperator):
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.CONFIGURE, (TL_OPERAND_TYPES.SUBFORMULA, instr.tlid), (TL_OPERAND_TYPES.DIRECT, 64), 64*boxqs))
            boxqs += 1
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.CONFIGURE, (TL_OPERAND_TYPES.SUBFORMULA, instr.tlid), (TL_OPERAND_TYPES.ATOMIC, 0), instr.interval.lb))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.CONFIGURE, (TL_OPERAND_TYPES.SUBFORMULA, instr.tlid), (TL_OPERAND_TYPES.ATOMIC, 1), instr.interval.ub))

    # for alias in aliases:
    #     cfg_instrs.append()

    spec_bin = bytearray()
    spec_header = b'C2P0 Version 0.0.0 Beta for R2U2 V3 Beta\x00'
    spec_bin.extend(cStruct('B').pack(len(spec_header)+1) + spec_header)
    [spec_bin.extend(cStruct('B').pack(len(x)+1) + x) for x in rtm_instrs]
    [spec_bin.extend(cStruct('B').pack(len(x)+1) + x) for x in cfg_instrs]
    spec_bin.extend(b'\x00')

    with open(filename,'wb') as f:
        f.write(spec_bin)
