from __future__ import annotations
from dataclasses import Field, dataclass
from dis import Instruction
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

class EngineTag(Enum):
    NA = 0 # Null instruction tag - acts as ENDSEQ
    SY = 1 # System commands - reserved for monitor control
    CG = 2 # Immediate Configuration Directive
    AT = 3 # Original Atomic Checker
    FT = 4 # MLTL Temporal logic engine (future time)
    PT = 4 # MLTL Temporal logic engine (past time)
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
    (C2POSignal, True):              BZOperator.ILOAD,
    (C2POSignal, False):             BZOperator.FLOAD,
    (C2POInteger, True):             BZOperator.ICONST,
    (C2POFloat, False):              BZOperator.FCONST,
    (C2POBitwiseNegate, True):       BZOperator.BWNEG,
    (C2POBitwiseAnd, True):          BZOperator.BWAND,
    (C2POBitwiseOr, True):           BZOperator.BWOR,
    (C2POBitwiseXor, True):          BZOperator.BWXOR,
    (C2POEqual, True):               BZOperator.IEQ,
    (C2POEqual, False):              BZOperator.FEQ,
    (C2PONotEqual, True):            BZOperator.INEQ,
    (C2PONotEqual, False):           BZOperator.FNEQ,
    (C2POGreaterThan, True):         BZOperator.IGT,
    (C2POGreaterThanOrEqual, False): BZOperator.FGT,
    (C2POLessThan, True):            BZOperator.ILT,
    (C2POLessThanOrEqual, False):    BZOperator.ILTE,
    (C2POArithmeticNegate, True):    BZOperator.INEG,
    (C2POArithmeticNegate, False):   BZOperator.FNEG,
    (C2POArithmeticAdd, True):       BZOperator.IADD,
    (C2POArithmeticAdd, False):      BZOperator.FADD,
    (C2POArithmeticSubtract, True):  BZOperator.ISUB,
    (C2POArithmeticSubtract, False): BZOperator.FSUB,
    (C2POArithmeticMultiply, True):  BZOperator.IMUL,
    (C2POArithmeticMultiply, False): BZOperator.FMUL,
    (C2POArithmeticDivide, True):    BZOperator.IDIV,
    (C2POArithmeticDivide, False):   BZOperator.FDIV,
    (C2POArithmeticModulo, False):   BZOperator.MOD,
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
    C2POBoolType: ATFilter.BOOL,
    C2POIntType: ATFilter.INT,
    C2POFloatType: ATFilter.FLOAT,
}


class TLOperandType(Enum):
    DIRECT      = 0b01
    ATOMIC      = 0b00
    SUBFORMULA  = 0b10
    NONE        = 0b11

TL_OPERAND_TYPE_MAP = {
    C2POBool: TLOperandType.DIRECT,
    C2POAtomicChecker: TLOperandType.ATOMIC,
}


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


class CGType(Enum):
    SCQ = 0
    LB = 1
    UB = 2
    
    def __str__(self) -> str:
        return self.name


class FieldType(Enum):
    ENGINE_TAG       = 0
    INSTR_SIZE       = 1
    BZ_ID            = 2
    BZ_OPERATOR      = 3
    BZ_STORE_ATOMIC  = 4
    BZ_ATOMIC_ID     = 5
    BZ_OPERAND_INT   = 6
    BZ_OPERAND_FLOAT = 7
    AT_VALUE_BOOL    = 8
    AT_VALUE_SIG     = 9
    AT_VALUE_INT     = 10
    AT_VALUE_FLOAT   = 11
    AT_REL_OP        = 12
    AT_FILTER        = 13
    AT_ID            = 14
    AT_COMPARE_VALUE_IS_SIGNAL = 15
    TL_ID            = 16
    TL_OPERATOR      = 17
    TL_OPERAND_TYPE  = 18
    TL_OPERAND_VALUE = 19

field_format_str_map = {
    FieldType.ENGINE_TAG:       "B",
    FieldType.INSTR_SIZE:       "B",
    FieldType.BZ_ID:            "B",
    FieldType.BZ_OPERATOR:      "i",
    FieldType.BZ_STORE_ATOMIC:  "B",
    FieldType.BZ_ATOMIC_ID:     "B",
    FieldType.BZ_OPERAND_INT:   "q",
    FieldType.BZ_OPERAND_FLOAT: "d",
    FieldType.AT_VALUE_BOOL:    "?xxxxxxx",
    FieldType.AT_VALUE_SIG:     "Bxxxxxxx",
    FieldType.AT_VALUE_INT:     "q",
    FieldType.AT_VALUE_FLOAT:   "d",
    FieldType.AT_REL_OP:        "i",
    FieldType.AT_FILTER:        "i",
    FieldType.AT_ID:            "B",
    FieldType.AT_COMPARE_VALUE_IS_SIGNAL: "B",
    FieldType.TL_ID:            "I",
    FieldType.TL_OPERATOR:      "i",
    FieldType.TL_OPERAND_TYPE:  "i",
    FieldType.TL_OPERAND_VALUE: "Bxxx",
}

def pack_field_struct(format_strs: Dict[FieldType, str], field_type: FieldType, value: Any) -> bytes:
    if field_type not in format_strs:
        logger.error(f"Field type {field_type} not in field format map.")
        return bytes()
    return CStruct(format_strs[field_type]).pack(value)
    

@dataclass
class ATInstruction():
    engine_tag: EngineTag
    id: int
    relational_operator: ATRelOp
    signal_id: int
    signal_type: ATFilter
    compare_value: Union[bool, int, float]
    compare_is_signal: bool
    atomic_id: int
    
@dataclass
class BZInstruction():
    engine_tag: EngineTag
    id: int
    operator: BZOperator
    store_atomic: bool
    atomic_id: int
    operand1: Union[None, int, float]
    operand2: Union[None, int, float]

    def __str__(self) -> str:
        field_strs: List[str] = []

        field_strs.append(f"{self.engine_tag.name}")
        field_strs.append(f"b{self.id:<2}")
        field_strs.append(f"{self.operator:6}")
        if self.operand1 is not None:
            field_strs.append(f"{self.operand1}")
        if self.operand2 is not None:
            field_strs.append(f"{self.operand2}")

        return " ".join(field_strs)

@dataclass
class TLInstruction():
    engine_tag: EngineTag
    id: int
    operator: TLOperator
    operand1_type: TLOperandType
    operand1_value: Any
    operand2_type: TLOperandType
    operand2_value: Any

    def __str__(self) -> str:
        field_strs: List[str] = []

        field_strs.append(f"{self.engine_tag.name}")
        field_strs.append(f"n{self.id:<2}")
        field_strs.append(f"{self.operator:6}")

        # if self.operator.is_temporal():
        #     field_strs.append(f"{}")

        if self.operand1_type == TLOperandType.DIRECT:
            field_strs.append(f"{self.operand1_value}")
        elif self.operand1_type == TLOperandType.ATOMIC:
            field_strs.append(f"a{self.operand1_value}")
        elif self.operand1_type == TLOperandType.SUBFORMULA:
            field_strs.append(f"n{self.operand1_value}")

        if self.operand2_type == TLOperandType.DIRECT:
            field_strs.append(f"{self.operand2_value}")
        elif self.operand2_type == TLOperandType.ATOMIC:
            field_strs.append(f"a{self.operand2_value}")
        elif self.operand2_type == TLOperandType.SUBFORMULA:
            field_strs.append(f"n{self.operand2_value}")

        return " ".join(field_strs)

@dataclass
class CGInstruction():
    engine_tag: EngineTag
    type: CGType
    instruction: TLInstruction

    def __str__(self) -> str:
        field_strs: List[str] = [f"{self.engine_tag.name}"]
        if self.type == CGType.SCQ:
            field_strs.append(f"{self.instruction.engine_tag}")
            field_strs.append(f"{self.type:3}")
            field_strs.append(f"n{self.instruction.operand1_value:<2}")
            field_strs.append(f"({self.instruction.id}, {self.instruction.operand2_value})")
        else:
            field_strs.append(f"{self.instruction.engine_tag}")
            field_strs.append(f"{self.type:3}")
            field_strs.append(f"n{self.instruction.operand1_value:<2}")
            field_strs.append(f"{self.instruction.id}")
        return " ".join(field_strs)


def generate_at_instruction(
    node: C2POExpression,
    context: C2POContext
) -> ATInstruction:
    expr = context.atomic_checkers[node.symbol]

    # we can do the following since it is type-correct
    expr = cast(C2PORelationalOperator, node)
    signal = cast(C2POSignal, expr.get_lhs())

    rhs = expr.get_rhs()
    if isinstance(rhs, C2POConstant):
        compare_value = rhs.value
    elif isinstance(rhs, C2POSignal):
        compare_value = rhs.signal_id
    else:
        logger.critical(f"Compare value for AT checker must be a constant or signal, got '{type(rhs)}' ({rhs}).\n\tWhy did this get past the type checker?")
        compare_value = 0

    return ATInstruction(
        EngineTag.AT,
        node.atomic_id,
        AT_REL_OP_MAP[expr], # type: ignore
        signal.signal_id,
        AT_FILTER_MAP[signal.type], # type: ignore
        compare_value,
        isinstance(expr.get_lhs(), C2POSignal),
        node.atomic_id
    )

def generate_bz_instruction(
    node: C2POExpression,
    context: C2POContext,
    instructions: Dict[C2POExpression, BZInstruction]
) -> BZInstruction:
    bzid = len(instructions)

    if isinstance(node, C2POSignal):
        operand1 = node.signal_id
        operand2 = 0
    elif isinstance(node, C2POInteger):
        operand1 = node.value
        operand2 = 0
    elif isinstance(node, C2POFloat):
        operand1 = node.value
        operand2 = 0
    elif node.num_children() == 1:
        operand1 = instructions[node.get_child(0)].id # type: ignore
        operand2 = 0
    elif node.num_children() == 2:
        operand1 = instructions[node.get_child(0)].id # type: ignore
        operand2 = instructions[node.get_child(0)].id # type: ignore
    else:
        operand1 = 0
        operand2 = 0

    return BZInstruction(
        EngineTag.BZ,
        bzid,
        BZ_OPERATOR_MAP[(type(node), is_integer_type(node.type))], # type: ignore
        node in context.atomics,
        max(node.atomic_id, 0),
        operand1,
        operand2
    )

def generate_tl_operand(
    operand: Optional[C2PONode],
    instructions: Dict[C2POExpression, TLInstruction]
) -> Tuple[TLOperandType, Any]:
    if isinstance(operand, C2POBool):
        operand_type = TLOperandType.DIRECT
        operand_value = operand.value
    elif operand in instructions:
        operand_type = TLOperandType.SUBFORMULA
        operand_value = instructions[operand].id
    else:
        operand_type = TLOperandType.NONE
        operand_value = 0

    return (operand_type, operand_value)

def generate_ft_instruction(
    node: C2POExpression, 
    instructions: Dict[C2POExpression, TLInstruction]
) -> TLInstruction:
    id = len(instructions)

    operand1_type, operand1_value = generate_tl_operand(node.get_child(0), instructions)
    operand2_type, operand2_value = generate_tl_operand(node.get_child(1), instructions)

    return TLInstruction(
        EngineTag.FT, 
        id, 
        FT_OPERATOR_MAP[type(node)], # type: ignore
        operand1_type,
        operand1_value,
        operand2_type,
        operand2_value
    )

def generate_pt_instruction(
    node: C2POExpression, 
    instructions: Dict[C2POExpression, TLInstruction]
) -> TLInstruction:
    id = len(instructions)

    operand1_type, operand1_value = generate_tl_operand(node.get_child(0), instructions)
    operand2_type, operand2_value = generate_tl_operand(node.get_child(1), instructions)

    return TLInstruction(
        EngineTag.PT, 
        id, 
        PT_OPERATOR_MAP[node], 
        operand1_type,
        operand1_value,
        operand2_type,
        operand2_value
    )

def generate_scq_instructions(
    node: C2POExpression,
    instructions: Dict[C2POExpression, TLInstruction]
) -> List[CGInstruction]:
    cg_scq = CGInstruction(
        EngineTag.CG,
        CGType.SCQ,
        TLInstruction(
            EngineTag.FT,
            node.scq[0],
            FTOperator.CONFIG,
            TLOperandType.SUBFORMULA,
            instructions[node].id,
            TLOperandType.DIRECT,
            node.scq[1]
        )
    )

    if not isinstance(node, C2POTemporalOperator):
        return [cg_scq]

    cg_lb = CGInstruction(
        EngineTag.CG,
        CGType.LB,
        TLInstruction(
            EngineTag.FT,
            node.interval.lb,
            FTOperator.CONFIG,
            TLOperandType.SUBFORMULA,
            instructions[node].id,
            TLOperandType.ATOMIC,
            0
        )
    )

    cg_ub = CGInstruction(
        EngineTag.CG,
        CGType.UB,
        TLInstruction(
            EngineTag.FT,
            node.interval.ub,
            FTOperator.CONFIG,
            TLOperandType.SUBFORMULA,
            instructions[node].id,
            TLOperandType.DIRECT,
            0
        )
    )

    return [cg_scq, cg_lb, cg_ub]


def generate_assembly(
    program: C2POProgram,
    context: C2POContext
):
    at_instructions: Dict[C2POExpression, ATInstruction] = {}
    bz_instructions: Dict[C2POExpression, BZInstruction] = {}
    ft_instructions: Dict[C2POExpression, TLInstruction] = {}
    pt_instructions: Dict[C2POExpression, TLInstruction] = {}
    cg_instructions: Dict[C2POExpression, List[CGInstruction]] = {}

    def _generate_assembly(node: C2PONode):
        if not isinstance(node, C2POExpression):
            return

        if node in context.atomics and context.is_future_time():
            ftid = len(ft_instructions)
            ft_instructions[node] = TLInstruction(
                EngineTag.FT, ftid, FTOperator.LOAD, 
                TLOperandType.ATOMIC, node.atomic_id,
                TLOperandType.NONE, 0
            )
            cg_instructions[node] = generate_scq_instructions(node, ft_instructions)
        elif node in context.atomics and context.is_past_time():
            ptid = len(pt_instructions)
            pt_instructions[node] = TLInstruction(
                EngineTag.PT, ptid, PTOperator.LOAD, 
                TLOperandType.ATOMIC, node.atomic_id,
                TLOperandType.NONE, 0
            )

        if node.engine == R2U2Engine.ATOMIC_CHECKER:
            at_instructions[node] = generate_at_instruction(node, context)
        elif node.engine == R2U2Engine.BOOLEANIZER:
            bz_instructions[node] = generate_bz_instruction(node, context, bz_instructions)
        elif node.engine == R2U2Engine.TEMPORAL_LOGIC and context.is_future_time():
            ft_instructions[node] = generate_ft_instruction(node, ft_instructions)
            cg_instructions[node] = generate_scq_instructions(node, ft_instructions)
        elif node.engine == R2U2Engine.TEMPORAL_LOGIC and context.is_past_time():
            pt_instructions[node] = generate_pt_instruction(node, pt_instructions)

    context.set_future_time() # need to set this to disambiguate PT/FT logical ops
    spec_section = program.get_future_time_spec_section()
    if spec_section:
        for node in postorder(spec_section):
            _generate_assembly(node)

    context.set_past_time() # need to set this to disambiguate PT/FT logical ops
    spec_section = program.get_past_time_spec_section()
    if spec_section:
        for node in postorder(spec_section):
            _generate_assembly(node)

    return (list(bz_instructions.values()) + 
            list(ft_instructions.values()) + 
            [cg_instr for cg_instrs in cg_instructions.values() for cg_instr in cg_instrs])


def pack_at_instruction(
    instruction: ATInstruction, 
    format_strs: Dict[FieldType, str]
) -> bytes:
    binary = bytes()

    binary += pack_field_struct(format_strs, FieldType.ENGINE_TAG, instruction.engine_tag)
    binary += pack_field_struct(format_strs, FieldType.AT_VALUE_INT, 0)
    binary += pack_field_struct(format_strs, FieldType.AT_REL_OP, instruction.relational_operator.value)
    binary += pack_field_struct(format_strs, FieldType.AT_FILTER, instruction.signal_type.value)
    binary += pack_field_struct(format_strs, FieldType.AT_VALUE_SIG, instruction.signal_id)
    binary += pack_field_struct(format_strs, FieldType.AT_ID, instruction.atomic_id)
    binary += pack_field_struct(format_strs, FieldType.AT_COMPARE_VALUE_IS_SIGNAL, instruction.compare_is_signal)
    binary += pack_field_struct(format_strs, FieldType.AT_ID, instruction.atomic_id)

    binary_len = CStruct("B").pack(len(binary)+1)
    return binary_len + binary

def pack_bz_instruction(
    instruction: BZInstruction, 
    format_strs: Dict[FieldType, str]
) -> bytes:
    binary = bytes()

    format_str = format_strs[FieldType.ENGINE_TAG]
    format_str += format_strs[FieldType.BZ_ID]
    format_str += format_strs[FieldType.BZ_OPERATOR]
    format_str += format_strs[FieldType.BZ_STORE_ATOMIC]
    format_str += format_strs[FieldType.BZ_ATOMIC_ID]
    format_str += format_strs[FieldType.BZ_OPERAND_FLOAT] if isinstance(instruction.operand1, float) else format_strs[FieldType.BZ_OPERAND_INT]
    format_str += format_strs[FieldType.BZ_OPERAND_FLOAT] if isinstance(instruction.operand2, float) else format_strs[FieldType.BZ_OPERAND_INT] 

    binary = CStruct(format_str).pack(
        instruction.engine_tag.value,
        instruction.id,
        instruction.operator.value,
        instruction.store_atomic,
        instruction.atomic_id,
        instruction.operand1,
        instruction.operand2
    )

    logger.debug(f" Packing: {instruction}")
    logger.debug(f"   {format_strs[FieldType.ENGINE_TAG]:2} {format_strs[FieldType.BZ_ID]:2} {format_strs[FieldType.BZ_OPERATOR]:2} {format_strs[FieldType.BZ_STORE_ATOMIC]:2} {format_strs[FieldType.BZ_ATOMIC_ID]:2} {format_strs[FieldType.BZ_OPERAND_FLOAT] if isinstance(instruction.operand1, float) else format_strs[FieldType.BZ_OPERAND_INT]:2} {format_strs[FieldType.BZ_OPERAND_FLOAT] if isinstance(instruction.operand2, float) else format_strs[FieldType.BZ_OPERAND_INT]:2}")
    logger.debug(f"   {instruction.engine_tag.value:<2} {instruction.id:<2} {instruction.operator.value:<2} {instruction.store_atomic:<2} {instruction.atomic_id:<2} {instruction.operand1:<2} {instruction.operand2:<2}")

    return binary

def pack_tl_instruction(
    instruction: TLInstruction, 
    format_strs: Dict[FieldType, str]
) -> bytes:
    binary = bytes()

    operand_format_str = format_strs[FieldType.TL_OPERAND_TYPE]
    operand_format_str += format_strs[FieldType.TL_OPERAND_VALUE]
    operand_struct = CStruct(operand_format_str)

    operand1_binary = operand_struct.pack(
        instruction.operand1_type.value,
        instruction.operand1_value
    )
    operand2_binary = operand_struct.pack(
        instruction.operand2_type.value,
        instruction.operand2_value
    )

    format_str = format_strs[FieldType.ENGINE_TAG]
    format_str += f"{operand_struct.size}s"
    format_str += f"{operand_struct.size}s"
    format_str += format_strs[FieldType.TL_ID]
    format_str += format_strs[FieldType.TL_OPERATOR]

    binary = CStruct(format_str).pack(
        instruction.engine_tag.value,
        operand1_binary,
        operand2_binary,
        instruction.id,
        instruction.operator.value,
    )

    logger.debug(f" Packing: {instruction}")
    logger.debug(f"   {format_strs[FieldType.ENGINE_TAG]:2} [{format_strs[FieldType.TL_OPERAND_TYPE]:2} {format_strs[FieldType.TL_OPERAND_VALUE]:4}] [{format_strs[FieldType.TL_OPERAND_TYPE]:2} {format_strs[FieldType.TL_OPERAND_VALUE]:4}] {format_strs[FieldType.TL_ID]:2} {format_strs[FieldType.TL_OPERATOR]:2}")
    logger.debug(f"   {instruction.engine_tag.value:<2} [{instruction.operand1_type.value:<2} {instruction.operand1_value:<4}] [{instruction.operand2_type.value:<2} {instruction.operand2_value:<4}] {instruction.id:<2} {instruction.operator.value:<2}")

    return binary

def pack_cg_instruction(
    instruction: CGInstruction, 
    format_strs: Dict[FieldType, str]
) -> bytes:
    binary = bytes()

    format_str = format_strs[FieldType.ENGINE_TAG]

    binary += CStruct(format_str).pack(
        instruction.engine_tag.value
    )

    binary += pack_tl_instruction(instruction.instruction, format_strs)

    logger.debug(f" Packing: {instruction}")
    logger.debug(f"   {format_strs[FieldType.ENGINE_TAG]:<2}")
    logger.debug(f"   {instruction.engine_tag.value:<2}")

    return binary

def pack_instruction(
    instruction: Union[ATInstruction, BZInstruction, TLInstruction, CGInstruction],
    format_strs: Dict[FieldType, str]
) -> bytes:
    if isinstance(instruction, ATInstruction):
        binary = pack_at_instruction(instruction, format_strs)
    elif isinstance(instruction, BZInstruction):
        binary = pack_bz_instruction(instruction, format_strs)
    elif isinstance(instruction, TLInstruction):
        binary = pack_tl_instruction(instruction, format_strs)
    elif isinstance(instruction, CGInstruction):
        binary = pack_cg_instruction(instruction, format_strs)
    else:
        logger.error(f"Invalid instruction type ({type(instruction)}).")
        binary = bytes()

    binary_len = CStruct("B").pack(len(binary)+1)
    return binary_len + binary

def pack_aliases(program: C2POProgram) -> bytes:
    binary = bytes()

    for spec in program.get_specs():
        if isinstance(spec, C2POSpecification):
            binary += f"F {spec.symbol} {spec.formula_number}".encode("ascii") + b"\x00"
            logger.debug(f" Packing: F {spec.symbol} {spec.formula_number}")
        elif isinstance(spec, C2POContract):
            binary += f"F {spec.symbol} {' '.join([str(f) for f in spec.formula_numbers])}".encode("ascii") +  b"\x00"
            logger.debug(f" Packing: F {spec.symbol} {' '.join([str(f) for f in spec.formula_numbers])}")

    return binary


def assemble(
    program: C2POProgram,
    context: C2POContext,
    quiet: bool
) -> bytes:
    check_sizes()
    assembly = generate_assembly(program, context)

    binary = bytes()
    binary_header = b"C2PO Version 1.0.0 for R2U2 V3\x00"
    binary += CStruct("B").pack(len(binary_header)+1) + binary_header

    for instr in assembly:
        binary += pack_instruction(instr, field_format_str_map)

    binary += b"\x00"
    binary += pack_aliases(program)
    binary += b"\x00"

    if not quiet:
        [print(instr) for instr in assembly]

    return binary
