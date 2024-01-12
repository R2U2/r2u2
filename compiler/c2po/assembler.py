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
    FORMULA        = 0b0100
    RATE           = 0b0101
    ABS_DIFF_ANGLE = 0b0110
    MOVAVG         = 0b0111
    EXACTLY_ONE_OF = 0b1000
    NONE_OF        = 0b1001
    ALL_OF         = 0b1010

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

def check_sizes():
    mem_ref_size = cStruct("I").size
    if mem_ref_size != 4:
        import warnings
        warnings.warn(f"MLTL memory refernce is 32-bit by default, but platform spcifies {mem_ref_size} bytes".format(), BytesWarning)

def assemble_bz(bzid: int, opcode: BZOpcode, param1: int|float, param2: int, store_at: bool, atid: int) -> bytes:
    bz_instruction = cStruct("BiBBqq") if isinstance(param1, int) else  cStruct("BiBBdq")
    return bz_instruction.pack(bzid, opcode.value, store_at, atid if atid >= 0 else 0, param1, param2)


def assemble_at(conditional, filter, sig_addr, atom_addr, comp_is_sig, comparison, filter_arg, aux_addr):
    at_instruction = cStruct('8s8siiBBBB')
    return at_instruction.pack(comparison, filter_arg, conditional.value, filter.value, sig_addr, atom_addr, comp_is_sig, aux_addr)


def assemble_ft(opcode, operand_1, operand_2, ref):
    # print(f"{FT_OP_CODES(opcode)} ({TL_OPERAND_TYPES(operand_1[0])}, {operand_1[1]}) ({TL_OPERAND_TYPES(operand_2[0])}, {operand_2[1]}), {ref}")

    # The module memoizes these by their description string so this isn't as
    # wasteful as it initially appears
    operand = cStruct('iBxxx')
    ft_instruction = cStruct(f"{operand.size}s{operand.size}sii")
    return ft_instruction.pack(
                        operand.pack(operand_1[0].value,operand_1[1]),
                        operand.pack(operand_2[0].value,operand_2[1]),
                        ref, opcode.value)


def assemble_pt(opcode, operand_1, operand_2, ref) -> bytes:
    # print(f"{PT_OP_CODES(opcode)} ({TL_OPERAND_TYPES(operand_1[0])}, {operand_1[1]}) ({TL_OPERAND_TYPES(operand_2[0])}, {operand_2[1]}), {ref}")

    # The module memoizes these by their description string so this isn't as
    # wasteful as it initially appears
    operand = cStruct('iBxxx')
    ft_instruction = cStruct(f"{operand.size}s{operand.size}sIi")
    return ft_instruction.pack(
                        operand.pack(operand_1[0].value,operand_1[1]),
                        operand.pack(operand_2[0].value,operand_2[1]),
                        ref, opcode.value)


def assemble_alias() -> None:
    pass


def assemble(filename: str, atasm: List[ATInstruction], bzasm: List[BZInstruction], ftasm: List[TLInstruction], ftscqasm: List[Tuple[int,int]], ptasm: List[TLInstruction],  aliases: List[str]):

    # Concatenate runtime instructions, assume V2 ordering
    # foo: List[Instruction] = atasm + bzasm + ftasm + ptasm

    check_sizes()

    # Create a list of runtime instructions and config instructions
    rtm_instrs: List[bytes] = []
    cfg_instrs: List[bytes] = []
    alias_defs: List[bytes] = []

    at_formula_instr: List[ATInstruction] = []

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
            filter_arg = cStruct("xxxxxxxx").pack()
        elif instr.filter == "int":
            filter = ATFilter.INT
            format = "q"
            filter_arg = cStruct("xxxxxxxx").pack()
        elif instr.filter == "float":
            filter = ATFilter.FLOAT
            format = "d"
            filter_arg = cStruct("xxxxxxxx").pack()
        elif instr.filter == "formula":
            at_formula_instr.append(instr)
            continue
        elif instr.filter == "rate":
            filter = ATFilter.RATE
            format = "d"
            filter_arg = cStruct("xxxxxxxx").pack()
        elif instr.filter == "movavg":
            filter = ATFilter.MOVAVG
            format = "d"
            if isinstance(instr.args[1], Integer):
                filter_arg = cStruct("q").pack(instr.args[1].value)
            else:
                raise NotImplementedError
        elif instr.filter == "abs_diff_angle":
            filter = ATFilter.ABS_DIFF_ANGLE
            format = "d"
            if isinstance(instr.args[1], Float):
                filter_arg = cStruct("d").pack(instr.args[1].value)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
        
        if isinstance(instr.args[0], Signal):
            sid = instr.args[0].sid
        elif isinstance(instr.args[0], Specification):
            if instr.args[0].formula_type == FormulaType.FT:
                sid = instr.args[0].ftid
            else:
                sid = instr.args[0].ptid
        else:
            raise NotImplementedError

        comp_to_sig = isinstance(instr.compare, Signal)

        if isinstance(instr.compare, Signal):
            comparison = cStruct("Bxxxxxxx").pack(instr.compare.sid)
        elif isinstance(instr.compare, Constant):
            comparison = cStruct(format).pack(instr.compare.value)
        else:
            raise NotImplementedError

        rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.AT.value) + assemble_at(conditional, filter, sid, instr.atid, comp_to_sig, comparison, filter_arg, instr.atid))
    
    for instr in bzasm:
        if isinstance(instr, Signal):
            if is_integer_type(instr.type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.ILOAD, instr.sid, 0, instr.atid > -1, instr.atid))
            elif is_float_type(instr.type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FLOAD, instr.sid, 0, instr.atid > -1, instr.atid))
            else:
                raise NotImplementedError
        elif isinstance(instr, Integer):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.ICONST, instr.value, 0, instr.atid > -1, instr.atid))
        elif isinstance(instr, Float):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FCONST, instr.value, 0, instr.atid > -1, instr.atid))
        elif isinstance(instr, BitwiseAnd):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.BWAND, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, BitwiseOr):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.BWOR, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, BitwiseXor):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.BWXOR, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, BitwiseNegate):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.BWNEG, instr.get_operand().bzid, 0, instr.atid > -1, instr.atid))
        elif isinstance(instr, ArithmeticAdd):
            if is_integer_type(instr.type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.IADD, instr.get_child(0).bzid, instr.get_child(1).bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FADD, instr.get_child(0).bzid, instr.get_child(1).bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, ArithmeticSubtract):
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.ISUB, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FSUB, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, ArithmeticMultiply):
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.IMUL, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FMUL, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, ArithmeticDivide):
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.IDIV, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FDIV, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, ArithmeticModulo):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.MOD, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, ArithmeticNegate):
            if is_integer_type(instr.get_operand().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.INEG, instr.get_operand().bzid, 0, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FNEG, instr.get_operand().bzid, 0, instr.atid > -1, instr.atid))
        elif isinstance(instr, Equal):
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.IEQ, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FEQ, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, NotEqual):
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.INEQ, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FNEQ, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, GreaterThan):
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.IGT, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FGT, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, LessThan):
            if is_integer_type(instr.get_lhs().type):
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.ILT, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
            else:
                rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.FLT, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, GreaterThanOrEqual):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.IGTE, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))
        elif isinstance(instr, LessThanOrEqual):
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.BZ.value) + assemble_bz(instr.bzid, BZOpcode.ILTE, instr.get_lhs().bzid, instr.get_rhs().bzid, instr.atid > -1, instr.atid))

    ft_offset = len(rtm_instrs)

    for instr in ftasm:
        if isinstance(instr, Atomic) or isinstance(instr, BZInstruction):  # Load
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.LOAD, (TLOperandType.ATOMIC, instr.atid), (TLOperandType.NOT_SET, 0), instr.ftid))
        elif isinstance(instr, Specification):  # End
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.RETURN, (TLOperandType.SUBFORMULA, instr.get_expr().ftid), (TLOperandType.DIRECT, instr.formula_number), instr.ftid))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ftid), (TLOperandType.ATOMIC, 2), instr.deadline))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ftid), (TLOperandType.ATOMIC, 3), instr.k_modes))

            for at_instr in at_formula_instr:
                if instr == at_instr.args[0]:
                    if isinstance(at_instr.rel_op, Equal):
                        conditional = ATCond.EQ
                    elif isinstance(at_instr.rel_op, NotEqual):
                        conditional = ATCond.NEQ
                    elif isinstance(at_instr.rel_op, GreaterThan):
                        conditional = ATCond.GT
                    elif isinstance(at_instr.rel_op, LessThan):
                        conditional = ATCond.LT
                    elif isinstance(at_instr.rel_op, GreaterThanOrEqual):
                        conditional = ATCond.GEQ
                    elif isinstance(at_instr.rel_op, LessThanOrEqual):
                        conditional = ATCond.LEQ
                    else:
                        raise NotImplementedError
                        
                    if at_instr.filter == "formula":
                        filter = ATFilter.FORMULA
                        format = "q"
                        filter_arg = cStruct("xxxxxxxx").pack()
                    else:
                        raise NotImplementedError

                    if isinstance(at_instr.args[0], Specification):
                        sid = at_instr.args[0].get_expr().ftid + ft_offset
                    else:
                        raise NotImplementedError

                    comp_to_sig = isinstance(at_instr.compare, Signal)

                    if isinstance(at_instr.compare, Signal):
                        comparison = cStruct("Bxxxxxxx").pack(at_instr.compare.sid)
                    elif isinstance(at_instr.compare, Constant):
                        comparison = cStruct(format).pack(at_instr.compare.value)
                    else:
                        raise NotImplementedError

                    rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.AT.value) + assemble_at(conditional, filter, sid, at_instr.atid, comp_to_sig, comparison, filter_arg, at_instr.atid))

        elif isinstance(instr, Global): # Globally
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.GLOBALLY, (TLOperandType.SUBFORMULA, instr.get_children()[0].ftid), (TLOperandType.NOT_SET, 0), instr.ftid))
        elif isinstance(instr, Until):  # Until
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.ftid)

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.ftid)

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.UNTIL, op1, op2, instr.ftid))
            pass
        elif isinstance(instr, LogicalNegate):  # Not
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.ftid)

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.NOT, op1, (TLOperandType.NOT_SET, 0), instr.ftid))
        elif isinstance(instr, LogicalAnd): # And
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.ftid)

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.ftid)

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.AND, op1, op2, instr.ftid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplementedError

        # Configure SCQ size and, if temporal, interval bounds
        cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ftid), (TLOperandType.DIRECT, ftscqasm[instr.ftid][1] - ftscqasm[instr.ftid][0]), ftscqasm[instr.ftid][0]))
        if isinstance(instr, TemporalOperator):
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ftid), (TLOperandType.ATOMIC, 0), instr.interval.lb))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_ft(FTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ftid), (TLOperandType.ATOMIC, 1), instr.interval.ub))

    pt_offset = len(rtm_instrs)

    boxqs = 1 # Number of boxqueus for running offsets
    for instr in ptasm:
        if isinstance(instr, Atomic) or isinstance(instr, BZInstruction):  # Load
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.LOAD, (TLOperandType.ATOMIC, instr.atid), (TLOperandType.NOT_SET, 0), instr.ptid))
        elif isinstance(instr, Specification):  # End
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.RETURN, (TLOperandType.SUBFORMULA, instr.get_expr().ptid), (TLOperandType.DIRECT, instr.formula_number), instr.ptid))

            for at_instr in at_formula_instr:
                if instr == at_instr:
                    if isinstance(at_instr.rel_op, Equal):
                        conditional = ATCond.EQ
                    elif isinstance(at_instr.rel_op, NotEqual):
                        conditional = ATCond.NEQ
                    elif isinstance(at_instr.rel_op, GreaterThan):
                        conditional = ATCond.GT
                    elif isinstance(at_instr.rel_op, LessThan):
                        conditional = ATCond.LT
                    elif isinstance(at_instr.rel_op, GreaterThanOrEqual):
                        conditional = ATCond.GEQ
                    elif isinstance(at_instr.rel_op, LessThanOrEqual):
                        conditional = ATCond.LEQ
                    else:
                        raise NotImplementedError
                        
                    if at_instr.filter == "formula":
                        filter = ATFilter.FORMULA
                        format = "q"
                        filter_arg = cStruct("xxxxxxxx").pack()
                    else:
                        raise NotImplementedError

                    if isinstance(at_instr.args[0], Specification):
                        sid = at_instr.args[0].get_expr().ptid + pt_offset
                    else:
                        raise NotImplementedError

                    comp_to_sig = isinstance(at_instr.compare, Signal)

                    if isinstance(at_instr.compare, Signal):
                        comparison = cStruct("Bxxxxxxx").pack(at_instr.compare.sid)
                    elif isinstance(at_instr.compare, Constant):
                        comparison = cStruct(format).pack(at_instr.compare.value)
                    else:
                        raise NotImplementedError

                    rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.AT.value) + assemble_at(conditional, filter, sid, at_instr.atid, comp_to_sig, comparison, filter_arg, at_instr.atid))

        elif isinstance(instr, Once): # Once
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.ONCE, (TLOperandType.SUBFORMULA, instr.get_children()[0].ptid), (TLOperandType.NOT_SET, 0), instr.ptid))
        elif isinstance(instr, Historical): # Historically
            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.HISTORICALLY, (TLOperandType.SUBFORMULA, instr.get_children()[0].ptid), (TLOperandType.NOT_SET, 0), instr.ptid))
        elif isinstance(instr, Since):  # Since
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.ptid)

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.ptid)

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.SINCE, op1, op2, instr.ptid))
            pass
        elif isinstance(instr, LogicalNegate):  # Not
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.ptid)

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.NOT, op1, (TLOperandType.NOT_SET, 0), instr.ptid))
        elif isinstance(instr, LogicalAnd): # And
            child = instr.get_children()[0]
            if isinstance(child, Bool):
                op1 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op1 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op1 = (TLOperandType.SUBFORMULA, child.ptid)

            child = instr.get_children()[1]
            if isinstance(child, Bool):
                op2 = (TLOperandType.DIRECT, child.value)
            # Atomic are access via loads which are created by atomic nodes
            # elif isinstance(child, Atomic):
            #     op2 = (TL_OPERAND_TYPES.ATOMIC, child.atid)
            else: # This is a bit overly permissive but we're assuming the compiler did its job
                op2 = (TLOperandType.SUBFORMULA, child.ptid)

            rtm_instrs.append(cStruct('B').pack(ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.AND, op1, op2, instr.ptid))
        elif isinstance(instr, SpecificationSet):
            # We no longer need these in V3
            continue
        else:
            raise NotImplementedError

        if isinstance(instr, TemporalOperator):
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ptid), (TLOperandType.DIRECT, 64), 64*boxqs))
            boxqs += 1
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ptid), (TLOperandType.ATOMIC, 0), instr.interval.lb))
            cfg_instrs.append(cStruct('BB').pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value) + assemble_pt(PTOpcode.CONFIGURE, (TLOperandType.SUBFORMULA, instr.ptid), (TLOperandType.ATOMIC, 1), instr.interval.ub))

    for alias in aliases:
        alias_defs.append(alias.encode('ascii'))

    spec_bin = bytearray()
    spec_header = b'C2P0 Version 1.0.0 for R2U2 V3\x00'
    spec_bin.extend(cStruct('B').pack(len(spec_header)+1) + spec_header)
    [spec_bin.extend(cStruct('B').pack(len(x)+1) + x) for x in rtm_instrs]
    [spec_bin.extend(cStruct('B').pack(len(x)+1) + x) for x in cfg_instrs]
    spec_bin.extend(b'\x00') # End of instruction segment
    [spec_bin.extend(x + b'\x00') for x in alias_defs]
    spec_bin.extend(b'\x00') # End of aux defs segment

    with open(filename,'wb') as f:
        f.write(spec_bin)
