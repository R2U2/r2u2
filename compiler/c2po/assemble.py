from __future__ import annotations
from enum import Enum
from struct import Struct as CStruct, calcsize
from typing import Union

from .logger import logger
from .ast import *

# See the documentation of the 'struct' package for info:
# https://docs.python.org/3/library/struct.html

def check_sizes():
    mem_ref_size = CStruct("I").size
    if mem_ref_size != 4:
        logger.warning(f"MLTL memory reference is 32-bit by default, but platform specifies {mem_ref_size} bytes")

    # if len(set([calcsize(f) for f in {AT_VALUE_BOOL_F, AT_VALUE_FLOAT_F, AT_VALUE_SIG_F, AT_VALUE_INT_F}])) > 1:
    #     logger.warning(f"Widths for AT value encodings not homogeneous.")

# The following classes define the allowable fields in an 
# assembly instruction. They are all either Enums or wrappers
# for a basic data type.
# Enum classes are used for things like opcodes.
# Other classes are used for values lie node IDs and constants.
# Each class must implement the following three methods to be valid
# for use in an assembly instruction:
# 1) 'assemble(self) -> bytes'
#    - Used for generating the binary representation of the field 
# 2) '__str__(self) -> str'
#    - Used for a human-readable format of the field
# 3) '__repr__(self) -> str'
#    - Used for a string format of the binary representation

class EngineTag(Enum):
    NA = 0 # Null instruction tag - acts as ENDSEQ
    SY = 1 # System commands - reserved for monitor control
    CG = 2 # Immediate Configuration Directive
    AT = 3 # Original Atomic Checker
    TL = 4 # MLTL Temporal logic engine
    BZ = 5 # Booleanizer

    def __str__(self) -> str:
        return self.name


class BZOperator(Enum):
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

    def is_constant(self) -> bool:
        return self is BZOperator.ICONST or self is BZOperator.FCONST
    
    def is_load(self) -> bool:
        return self is BZOperator.ILOAD or self is BZOperator.FLOAD

    def __str__(self) -> str:
        return self.name.lower()

BZ_OPERATOR_MAP = {
    # (node_type, is_int_type): BZOperator
    (C2POSignal, True):  BZOperator.ILOAD,
    (C2POSignal, True):  BZOperator.FLOAD,
    (C2POInteger, True): BZOperator.ICONST,
    (C2POFloat, True):   BZOperator.FCONST,
    (C2POArithmeticAdd, True):  BZOperator.IADD,
    (C2POArithmeticAdd, False): BZOperator.FADD,
    Any: BZOperator.NONE
}


class ATRelOp(Enum):
    EQ   = 0b000
    NEQ  = 0b001
    LT   = 0b010
    LEQ  = 0b011
    GT   = 0b100
    GEQ  = 0b101
    NONE = 0b111

AT_REL_OP_MAP = {
    C2POEqual:           ATRelOp.EQ,
    C2PONotEqual:        ATRelOp.NEQ,
    C2POLessThan:        ATRelOp.LT,
    C2POLessThanOrEqual: ATRelOp.LEQ,
    C2POGreaterThan:     ATRelOp.GT,
    C2POGreaterThanOrEqual: ATRelOp.GEQ,
    Any: ATRelOp.NONE
}


class ATFilter(Enum):
    NONE           = 0b0000
    BOOL           = 0b0001
    INT            = 0b0010
    FLOAT          = 0b0011
    FORMULA        = 0b0100
    # RATE           = 0b0101
    # ABS_DIFF_ANGLE = 0b0110
    # MOVAVG         = 0b0111
    # EXACTLY_ONE_OF = 0b1000
    # NONE_OF        = 0b1001
    # ALL_OF         = 0b1010

AT_FILTER_MAP = {
    C2POBool: ATFilter.BOOL,
    C2POInteger: ATFilter.INT,
    C2POFloat: ATFilter.FLOAT,
    C2POSpecification: ATFilter.FORMULA,
    Any: ATFilter.NONE
}


class TLOperandType(Enum):
    DIRECT      = 0b01
    ATOMIC      = 0b00
    SUBFORMULA  = 0b10
    NONE        = 0b11

TL_OPERAND_TYPE_MAP = {
    C2POBool: TLOperandType.DIRECT,
    C2POAtomicChecker: TLOperandType.ATOMIC,
    Any: TLOperandType.NONE
}

def get_tl_operand(
    operand: Optional[C2PONode], 
    instr: TLInstruction
) -> Tuple[TLOperandType, Union[int, float]]:
    """Computes the operand type and value of the given C2PONode and Instruction."""
    if isinstance(operand, C2POBool):
        return (TLOperandType.DIRECT, operand.value)
    elif isinstance(operand, C2POAtomicChecker):
        return (TLOperandType.ATOMIC, operand.atomic_id)
    elif isinstance(operand, C2PONode):
        return (TLOperandType.SUBFORMULA, instr.tlid)
    else:
        return (TLOperandType.NONE, 0)


class FTOperator(Enum):
    NOP       = 0b11111
    CONFIG    = 0b11110
    LOAD      = 0b11101
    RETURN    = 0b11100
    GLOBAL    = 0b11010
    UNTIL     = 0b11001
    NOT       = 0b10111
    AND       = 0b10110

    def is_temporal(self) -> bool:
        return self is FTOperator.GLOBAL or self is FTOperator.UNTIL

    def is_load(self) -> bool:
        return self is FTOperator.LOAD

    def __str__(self) -> str:
        return self.name.lower()

FT_OPERATOR_MAP = {
    C2POSpecification: FTOperator.RETURN,
    C2POGlobal: FTOperator.GLOBAL,
    C2POUntil: FTOperator.UNTIL,
    C2POLogicalNegate: FTOperator.NOT,
    C2POLogicalAnd: FTOperator.AND,
    Any: FTOperator.NOP
}


class PTOperator(Enum):
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

    def is_temporal(self) -> bool:
        return self == PTOperator.ONCE or self == PTOperator.HISTORICALLY or self == PTOperator.SINCE

    def is_load(self) -> bool:
        return self is PTOperator.LOAD
    
PT_OPERATOR_MAP = {
    Any: PTOperator.NOP
}


Operator = Union[FTOperator, PTOperator, BZOperator]
TLOperator = Union[FTOperator, PTOperator]


class FieldType(Enum):
    ENGINE_TAG      = 0
    INSTR_SIZE      = 1
    BZ_ID           = 2
    BZ_OPERATOR     = 3
    BZ_STORE_ATOMIC = 3
    BZ_ATOMIC_ID    = 4
    BZ_PARAM_INT    = 5
    BZ_PARAM_FLOAT  = 6
    AT_VALUE_BOOL   = 7
    AT_VALUE_SIG    = 8
    AT_VALUE_INT    = 9
    AT_VALUE_FLOAT  = 10
    AT_REL_OP       = 11
    AT_FILTER       = 12
    AT_ID           = 13
    AT_COMPARE_VALUE_IS_SIGNAL = 14
    TL_ID           = 15
    TL_OPERATOR     = 16
    TL_OPERAND_TYPE = 17
    TL_OPERAND_ID   = 18

field_format_str_map = {
    FieldType.ENGINE_TAG: "B",
    FieldType.INSTR_SIZE: "B",
    FieldType.BZ_ID:           "B",
    FieldType.BZ_OPERATOR:     "i",
    FieldType.BZ_STORE_ATOMIC: "B",
    FieldType.BZ_ATOMIC_ID:    "B",
    FieldType.BZ_PARAM_INT:    "i",
    FieldType.BZ_PARAM_FLOAT:  "d",
    FieldType.AT_VALUE_BOOL:  "?xxxxxxx",
    FieldType.AT_VALUE_SIG:   "Bxxxxxxx",
    FieldType.AT_VALUE_INT:   "q",
    FieldType.AT_VALUE_FLOAT: "d",
    FieldType.AT_REL_OP:      "i",
    FieldType.AT_FILTER:      "i",
    FieldType.AT_ID:          "B",
    FieldType.AT_COMPARE_VALUE_IS_SIGNAL: "B",
    FieldType.TL_ID:           "I",
    FieldType.TL_OPERATOR:     "i",
    FieldType.TL_OPERAND_TYPE: "i",
    FieldType.TL_OPERAND_ID:   "Bxxx",
}


class Instruction():

    def __init__(self) -> None:
        self.fields = []

    def assemble(self) -> bytes:
        binary = bytes()
        for field_type, field_value in self.fields:
            format_str = field_format_str_map[field_type]
            binary += CStruct(format_str).pack(field_value)

        instr_size_format_str = field_format_str_map[FieldType.INSTR_SIZE]
        instr_size = CStruct(instr_size_format_str).pack(len(binary) + 1)
        
        return instr_size + binary

    def __str__(self) -> str:
        return " ".join([str(f) for f in self.fields])

    def __repr__(self) -> str:
        return " ".join([repr(f) for f in self.fields])

class BZInstruction(Instruction):

    def __init__(
        self, 
        id: int, 
        node: C2POExpression,
        context: C2POContext
    ):
        self.engine_tag = EngineTag.BZ
        self.bzid = id
        self.operator = BZ_OPERATOR_MAP[(type(node), is_integer_type(node.type))]
        self.store_atomic = node in context.atomics
        self.atomic_id = node.atomic_id

        # if node.num_children() > 0:
        #     self.param1 = BZParameter(node.get_child(0))
        # elif node.num_children() > 1:
        #     pass
        # else:
        #     pass

        self.fields = [
            (FieldType.ENGINE_TAG, self.engine_tag), 
            (FieldType.BZ_ID, self.bzid),
            (FieldType.BZ_OPERATOR, self.operator),
            (FieldType.BZ_STORE_ATOMIC, self.store_atomic),
            (FieldType.BZ_ATOMIC_ID, self.atomic_id),
            (FieldType.BZ_PARAM_INT, 0),
            (FieldType.BZ_PARAM_INT, 0),
        ]

    def __str__(self) -> str:
        s = f"{self.engine_tag} b{self.bzid} {self.operator:6} "
        return s

class ATInstruction(Instruction):

    def __init__(
        self, 
        node: C2POExpression,
        context: C2POContext
    ):
        expr = context.atomic_checkers[node.symbol]

        # we can do the following casts since it is type-correct
        relational_expr = cast(C2PORelationalOperator, expr)
        lhs = cast(C2POSignal, relational_expr.get_lhs())
        rhs = relational_expr.get_rhs()

        if isinstance(rhs, C2POConstant):
            compare_value = rhs.value
            compare_value_is_sig = False
        elif isinstance(rhs, C2POSignal):
            compare_value = rhs.signal_id
            compare_value_is_sig = True
        else:
            logger.critical(f"Compare value for AT checker must be a constant or signal, got '{type(rhs)}' ({rhs}).\n\tWhy did this get past the type checker?")
            compare_value = 0
            compare_value_is_sig = False

        self.fields = [
            EngineTag.AT, 
            compare_value,
            0, # TODO: remove support for this
            AT_REL_OP_MAP[type(relational_expr)],
            AT_FILTER_MAP[type(lhs)],
            lhs.signal_id,
            node.atomic_id, 
            compare_value_is_sig,
            node.atomic_id
        ]

class TLInstruction(Instruction):

    def __init__(
        self, 
        id: int,
        node: C2PONode,
        context: C2POContext,
        instructions: InstructionDict
    ):
        self.engine_tag = EngineTag.TL
        self.tlid = id

        if context.is_future_time() and node in context.atomics:
            self.operator = FTOperator.LOAD
        elif context.is_past_time() and node in context.atomics:
            self.operator = PTOperator.LOAD
        elif context.is_future_time():
            self.operator = FT_OPERATOR_MAP[type(node)]
        else:
            self.operator = PT_OPERATOR_MAP[type(node)]

        operand1 = node.get_child(0)
        if isinstance(operand1, C2POBool):
            self.operand1_type = TLOperandType.DIRECT
            self.operand1_value = operand1.value
        elif node in context.atomics: # then we are a load
            self.operand1_type = TLOperandType.ATOMIC
            self.operand1_value = node.atomic_id
        elif operand1 in instructions:
            self.operand1_type = TLOperandType.SUBFORMULA

            (compute, load) = instructions[operand1]
            if load:
                self.operand1_value = load.tlid
            else:
                compute = cast(TLInstruction, compute)
                self.operand1_value = compute.tlid
        else:
            self.operand1_type = TLOperandType.NONE
            self.operand1_value = 0

        operand2 = node.get_child(1)
        if isinstance(operand2, C2POBool):
            self.operand2_type = TLOperandType.DIRECT
            self.operand2_value = operand2.value
        elif operand2 in instructions:
            self.operand2_type = TLOperandType.SUBFORMULA

            (compute, load) = instructions[operand2]
            if load:
                self.operand2_value = load.tlid
            else:
                compute = cast(TLInstruction, compute)
                self.operand2_value = compute.tlid
        else:
            self.operand2_type = TLOperandType.NONE
            self.operand2_value = 0

        self.fields = [
            self.engine_tag, 
            self.operand1_type, self.operand1_value,
            self.operand2_type, self.operand2_value,
            self.tlid, 
            self.operator
        ]

    def __str__(self) -> str:
        s = f"{self.engine_tag} n{self.tlid} {self.operator:6} "

        if self.operand1_type == TLOperandType.DIRECT:
            s += f"{self.operand1_value} "
        elif self.operand1_type == TLOperandType.ATOMIC:
            s += f"a{self.operand1_value} "
        elif self.operand1_type == TLOperandType.SUBFORMULA:
            s += f"n{self.operand1_value} "

        if self.operand2_type == TLOperandType.DIRECT:
            s += f"{self.operand2_value} "
        elif self.operand2_type == TLOperandType.ATOMIC:
            s += f"a{self.operand2_value} "
        elif self.operand2_type == TLOperandType.SUBFORMULA:
            s += f"n{self.operand2_value} "

        return s

# this maps expression nodes to a pair (compute, load) where `compute` is the 
# instruction that computes the value for the nodes and `load` is an instruction
# that loads that value from the atomics vector in the TL engine
InstructionDict = Dict[C2POExpression, Tuple[Instruction, Optional[TLInstruction]]]

def generate_assembly(
    program: C2POProgram,
    context: C2POContext
) -> List[Instruction]:
    bzid, atid, ftid, ptid = 0, 0, 0, 0

    instructions: InstructionDict = {}

    at_instructions = []
    bz_instructions = []
    ft_instructions = []
    pt_instructions = []

    def generate_assembly_util(node: C2PONode):
        nonlocal ftid, ptid

        if not isinstance(node, C2POExpression):
            return

        if node in context.atomics and context.is_future_time():
            load_instruction = TLInstruction(ftid, node, context, instructions)
            ftid += 1
        elif node in context.atomics and context.is_past_time():
            load_instruction = TLInstruction(ptid, node, context, instructions)
            ptid += 1
        else:
            load_instruction = None

        if node.engine == R2U2Engine.ATOMIC_CHECKER:
            compute_instruction = ATInstruction(node, context)
        elif node.engine == R2U2Engine.TEMPORAL_LOGIC and context.is_future_time():
            compute_instruction = TLInstruction(ftid, node, context, instructions)
            ftid += 1
        elif node.engine == R2U2Engine.TEMPORAL_LOGIC and context.is_past_time():
            compute_instruction = TLInstruction(ptid, node, context, instructions)
        elif node.engine == R2U2Engine.BOOLEANIZER:
            compute_instruction = BZInstruction(bzid, node, context)
        else:
            print(type(node))
            raise NotImplementedError

        print(compute_instruction)
        if load_instruction:
            print(load_instruction)

        instructions[node] = (compute_instruction, load_instruction)

    context.set_future_time() # need to set this to disambiguate PT/FT logical ops
    spec_section = program.get_future_time_spec_section()
    if spec_section:
        postorder(spec_section, generate_assembly_util)

    context.set_past_time() # need to set this to disambiguate PT/FT logical ops
    spec_section = program.get_past_time_spec_section()
    if spec_section:
        postorder(spec_section, generate_assembly_util)

    return []


def assemble(
    program: C2POProgram,
    context: C2POContext,
    quiet: bool
) -> bytes:
    check_sizes()
    generate_assembly(program, context)
    return bytes()