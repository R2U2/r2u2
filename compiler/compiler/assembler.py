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
    RATE           = 0b0100
    ABS_DIFF_ANGLE = 0b0101
    MOVAVG         = 0b0110
    EXACTLY_ONE_OF = 0b0111
    NONE_OF        = 0b1000
    ALL_OF         = 0b1001

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


def assemble_at(conditional: AT_COND, filter: AT_FILTER, sig_addr: int, atom_addr: int, comp_is_sig: bool, comparison: bytes):
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
        else:
            raise NotImplementedError

        if instr.filter == "bool":
            filter = AT_FILTER.BOOL
            format = "?xxxxxxx"
        elif instr.filter == "int":
            filter = AT_FILTER.INT
            format = "q"
        elif instr.filter == "float":
            filter = AT_FILTER.FLOAT
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
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

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
                raise NotImplementedError
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
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FT_OP_CODES.AND, op1, op2, instr.tlid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplementedError

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
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

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
                raise NotImplementedError
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
                raise NotImplementedError

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TL_OPERAND_TYPES.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            elif isinstance(child, TLInstruction): # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TL_OPERAND_TYPES.SUBFORMULA, child.tlid)
            else:
                raise NotImplementedError

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PT_OP_CODES.AND, op1, op2, instr.tlid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplementedError

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
