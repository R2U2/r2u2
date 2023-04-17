from __future__ import annotations
from typing import Sequence, Dict, List, Tuple
from enum import Enum
from struct import Struct as cStruct
from .ast import *


class ENGINE_TAGS(Enum):
    NA = 0 # Null instruction tag - acts as ENDSEQ
    SY = 1 # System commands - reserved for monitor control
    CG = 2 # Immediate Configuration Directive
    AT = 3 # Original Atomic Checker
    TL = 4 # MLTL Temporal logic engine
    BZ = 5 # Booleanizer

class BZOpcode(Enum):
    NONE    = 0b000000
    ILOAD   = 0b000001
    FLOAD   = 0b000010
    ICONST  = 0b000011
    FCONST  = 0b000100
    BWNEG   = 0b000101
    BWAND   = 0b000110
    BWOR    = 0b000111
    BWXOR   = 0b001000
    IEQ     = 0b001001
    FEQ     = 0b001010
    INEQ    = 0b001011
    FNEQ    = 0b001100
    IGT     = 0b001101
    FGT     = 0b001110
    IGTE    = 0b001111
    ILT     = 0b010000
    FLT     = 0b010001
    ILTE    = 0b010010
    INEG    = 0b010011
    FNEG    = 0b010100
    IADD    = 0b010101
    FADD    = 0b010110
    ISUB    = 0b010111
    FSUB    = 0b011000
    IMUL    = 0b011001
    FMUL    = 0b011010
    IDIV    = 0b011011
    FDIV    = 0b011100
    MOD     = 0b011101

class ATCond(Enum):
    EQ  = 0b000
    NEQ = 0b001
    LT  = 0b010
    LEQ = 0b011
    GT  = 0b100
    GEQ = 0b101

class ATFilter(Enum):
    BOOL           = 0b0001
    INT            = 0b0010
    FLOAT          = 0b0011
    RATE           = 0b0100
    ABS_DIFF_ANGLE = 0b0101
    MOVAVG         = 0b0110
    EXACTLY_ONE_OF = 0b0111
    NONE_OF        = 0b1000
    ALL_OF         = 0b1001

class TLOperandType(Enum):
    DIRECT      = 0b01
    ATOMIC      = 0b00
    SUBFORMULA  = 0b10
    NOT_SET     = 0b11

class FTOpcode(Enum):
    NOP       = 0b11111
    CONFIGURE = 0b11110
    LOAD      = 0b11101
    RETURN    = 0b11100
    GLOBALLY  = 0b11010
    UNTIL     = 0b11001
    NOT       = 0b10111
    AND       = 0b10110

class PTOpcode(Enum):
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


def assemble_bz(bzid: int, opcode: BZOpcode, param1: bytes, param2: bytes|None, store_at: bool, atid: int) -> bytes:
    if param2 is None:
        bz_instruction = cStruct("iiBB4sxxxx")
        return bz_instruction.pack(bzid, opcode.value, store_at, atid if atid >= 0 else 0, param1)
    else:
        bz_instruction = cStruct("iiBB4s4s")
        return bz_instruction.pack(bzid, opcode.value, store_at, atid if atid >= 0 else 0, param1, param2)



def assemble_at(conditional: ATCond, filter: ATFilter, sig_addr: int, atom_addr: int, comp_is_sig: bool, comparison: bytes):
    at_instruction = cStruct('iiBBBxxxxx8sd')
    return at_instruction.pack(conditional.value, filter.value, sig_addr, atom_addr, comp_is_sig, comparison, 0.00001)


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


def assemble_pt(opcode, operand_1, operand_2, ref) -> bytes:
    # print(f"{PT_OP_CODES(opcode)} ({TL_OPERAND_TYPES(operand_1[0])}, {operand_1[1]}) ({TL_OPERAND_TYPES(operand_2[0])}, {operand_2[1]}), {ref}")

    # The module memoizes these by their description string so this isn't as
    # wasteful as it initially appears
    operand = cStruct('iBxxx')
    ft_instruction = cStruct(f"i{operand.size}s{operand.size}sN")
    return ft_instruction.pack(opcode.value,
                        operand.pack(operand_1[0].value,operand_1[1]),
                        operand.pack(operand_2[0].value,operand_2[1]),
                        ref)


def assemble_alias() -> None:
    pass


def assemble(filename: str, atasm: List[ATInstruction], bzasm: List[BZInstruction], ftasm: List[TLInstruction], ftscqasm: List[Tuple[int,int]], ptasm: List[TLInstruction],  aliases: List[str]):

    # Concatenate runtime instructions, assume V2 ordering
    # foo: List[Instruction] = atasm + bzasm + ftasm + ptasm

    # Create a list of runtime instructions and config instructions
    rtm_instrs: List[bytes] = []
    cfg_instrs: List[bytes] = []

    for instr in atasm:

        if isinstance(instr.rel_op, Equal):
            conditional = ATCond.EQ
        elif isinstance(instr.rel_op, NotEqual):
            conditional = ATCond.NEQ
        elif isinstance(instr.rel_op, GreaterThan):
            conditional = ATCond.GT
        elif isinstance(instr.rel_op, LessThan):
            conditional = ATCond.LT
        elif isinstance(instr.rel_op, GreaterThanOrEqual):
            conditional = ATCond.GEQ
        elif isinstance(instr.rel_op, LessThanOrEqual):
            conditional = ATCond.LEQ
        else:
            raise NotImplementedError

        if instr.filter == "bool":
            filter = ATFilter.BOOL
            format = "?xxxxxxx"
        elif instr.filter == "int":
            filter = ATFilter.INT
            format = "q"
        elif instr.filter == "float":
            filter = ATFilter.FLOAT
            format = "d"
        else: 
            raise NotImplementedError

        comp_to_sig = isinstance(instr.compare, Signal)
        if isinstance(instr.compare, Signal):
            argument = cStruct("Bxxxxxxx").pack(instr.compare.sid)
        elif isinstance(instr.compare, Constant):
            argument = cStruct(format).pack(instr.compare.value)
        else:
            raise NotImplementedError

        if isinstance(instr.args[0], Signal):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.AT.value) + assemble_at(conditional, filter, instr.args[0].sid, instr.atid, comp_to_sig, argument))
        else:
            # first arg to filter needs to be signal, should be caught by type checker
            raise NotImplementedError
    # end atasm


    for instr in bzasm:
        if isinstance(instr, Signal):
            if is_integer_type(instr.type):
                param = cStruct("B").pack(instr.sid)
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.ILOAD, param, None, instr.atid > -1, instr.atid))
            elif is_float_type(instr.type):
                param = cStruct("B").pack(instr.sid)
                rtm_instrs.append(assemble_bz(instr.bzid, BZOpcode.FLOAD, param, None, instr.atid > -1, instr.atid))
            else:
                raise NotImplementedError
        elif isinstance(instr, GreaterThan):
            param1 = cStruct("B").pack(instr.get_lhs().bzid)
            param2 = cStruct("B").pack(instr.get_rhs().bzid)
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.IGT, param1, param2, instr.atid > -1, instr.atid))


    for instr in ftasm:
        if isinstance(instr, Atomic) or isinstance(instr, BZInstruction):  # Load
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.LOAD, (TLOperandType.ATOMIC, instr.atid), (TLOperandType.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Specification):  # End
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.RETURN, (TLOperandType.SUBFORMULA, instr.get_expr().tlid), (TLOperandType.DIRECT, instr.formula_number), instr.tlid))
        elif isinstance(instr, Global): # Globally
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.GLOBALLY, (TLOperandType.SUBFORMULA, instr.get_children()[0].tlid), (TLOperandType.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Until):  # Until
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.UNTIL, op1, op2, instr.tlid))
            pass
        elif isinstance(instr, LogicalNegate):  # Not
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.NOT, op1, (TLOperandType.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, LogicalAnd): # And
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.AND, op1, op2, instr.tlid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplementedError

        # Configure SCQ size and, if temporal, interval bounds
        cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.tlid), (TLOperandType.DIRECT, ftscqasm[instr.tlid][1] - ftscqasm[instr.tlid][0]), ftscqasm[instr.tlid][0]))
        if isinstance(instr, TemporalOperator):
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.tlid), (TLOperandType.ATOMIC, 0), instr.interval.lb))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.tlid), (TLOperandType.ATOMIC, 1), instr.interval.ub))

    boxqs = 1 # Number of boxqueus for running offsets
    for instr in ptasm:
        if isinstance(instr, Atomic):  # Load
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.LOAD, (TLOperandType.ATOMIC, instr.atid), (TLOperandType.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Specification):  # End
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.RETURN, (TLOperandType.SUBFORMULA, instr.get_expr().tlid), (TLOperandType.DIRECT, instr.formula_number), instr.tlid))
        elif isinstance(instr, Once): # Once
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.ONCE, (TLOperandType.SUBFORMULA, instr.get_children()[0].tlid), (TLOperandType.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Historical): # Historically
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.HISTORICALLY, (TLOperandType.SUBFORMULA, instr.get_children()[0].tlid), (TLOperandType.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, Since):  # Since
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.SINCE, op1, op2, instr.tlid))
            pass
        elif isinstance(instr, LogicalNegate):  # Not
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.NOT, op1, (TLOperandType.NOT_SET, 0), instr.tlid))
        elif isinstance(instr, LogicalAnd): # And
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.AND, op1, op2, instr.tlid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplementedError

        if isinstance(instr, TemporalOperator):
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.tlid), (TLOperandType.DIRECT, 64), 64*boxqs))
            boxqs += 1
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.tlid), (TLOperandType.ATOMIC, 0), instr.interval.lb))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.tlid), (TLOperandType.ATOMIC, 1), instr.interval.ub))

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
