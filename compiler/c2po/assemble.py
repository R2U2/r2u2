from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from struct import Struct as CStruct
from typing import Any, Optional, Union, cast

from c2po import cpt, log, types

# See the documentation of the 'struct' package for info:
# https://docs.python.org/3/library/struct.html

MODULE_CODE = "ASM"
ENDIAN = "<" # Little Endian


def check_sizes():
    mem_ref_size = CStruct("I").size
    if mem_ref_size != 4:
        log.warning(
            MODULE_CODE,
            f"MLTL memory reference is 32-bit by default, but platform specifies {mem_ref_size} bytes",
        )


class EngineTag(Enum):
    NA = 0  # Null instruction tag - acts as ENDSEQ
    SY = 1  # System commands - reserved for monitor control
    CG = 2  # Immediate Configuration Directive
    AT = 3  # Original Atomic Checker
    TL = 4  # MLTL Temporal logic engine
    BZ = 5  # Booleanizer

    def __str__(self) -> str:
        return self.name


class BZOperator(Enum):
    NONE = 0b000000
    ILOAD = 0b000001
    FLOAD = 0b000010
    ICONST = 0b000011
    FCONST = 0b000100
    STORE = 0b000101
    BWNEG = 0b000110
    BWAND = 0b000111
    BWOR = 0b001000
    BWXOR = 0b001001
    IEQ = 0b001010
    FEQ = 0b001011
    INEQ = 0b001100
    FNEQ = 0b001101
    IGT = 0b001110
    FGT = 0b001111
    IGTE = 0b010000
    FGTE = 0b010001
    ILT = 0b010010
    FLT = 0b010011
    ILTE = 0b010100
    FLTE = 0b010101
    INEG = 0b010110
    FNEG = 0b010111
    IADD = 0b011000
    FADD = 0b011001
    ISUB = 0b011010
    FSUB = 0b011011
    IMUL = 0b011100
    FMUL = 0b011101
    IDIV = 0b011110
    FDIV = 0b011111
    MOD = 0b100000
    IPOW  = 0b100001
    FPOW  = 0b100010
    ISQRT = 0b100011
    FSQRT = 0b100100
    IABS = 0b100101
    FABS = 0b100110
    PREV = 0b100111


    def is_constant(self) -> bool:
        return self is BZOperator.ICONST or self is BZOperator.FCONST

    def is_load(self) -> bool:
        return self is BZOperator.ILOAD or self is BZOperator.FLOAD

    def __str__(self) -> str:
        return self.name.lower()


# (OperatorType, Is integer variant) |-> BZOperator
BZ_OPERATOR_MAP: dict[tuple[cpt.OperatorKind, bool], BZOperator] = {
    (cpt.OperatorKind.BITWISE_NEGATE, True): BZOperator.BWNEG,
    (cpt.OperatorKind.BITWISE_AND, True): BZOperator.BWAND,
    (cpt.OperatorKind.BITWISE_OR, True): BZOperator.BWOR,
    (cpt.OperatorKind.BITWISE_XOR, True): BZOperator.BWXOR,
    (cpt.OperatorKind.ARITHMETIC_ADD, True): BZOperator.IADD,
    (cpt.OperatorKind.ARITHMETIC_ADD, False): BZOperator.FADD,
    (cpt.OperatorKind.ARITHMETIC_SUBTRACT, True): BZOperator.ISUB,
    (cpt.OperatorKind.ARITHMETIC_SUBTRACT, False): BZOperator.FSUB,
    (cpt.OperatorKind.ARITHMETIC_MULTPLY, True): BZOperator.IMUL,
    (cpt.OperatorKind.ARITHMETIC_MULTPLY, False): BZOperator.FMUL,
    (cpt.OperatorKind.ARITHMETIC_DIVIDE, True): BZOperator.IDIV,
    (cpt.OperatorKind.ARITHMETIC_DIVIDE, False): BZOperator.FDIV,
    (cpt.OperatorKind.ARITHMETIC_MODULO, True): BZOperator.MOD,
    (cpt.OperatorKind.ARITHMETIC_POWER, True): BZOperator.IPOW,
    (cpt.OperatorKind.ARITHMETIC_POWER, False): BZOperator.FPOW,
    (cpt.OperatorKind.ARITHMETIC_SQRT, True): BZOperator.ISQRT,
    (cpt.OperatorKind.ARITHMETIC_SQRT, False): BZOperator.FSQRT,
    (cpt.OperatorKind.ARITHMETIC_ABS, True): BZOperator.IABS,
    (cpt.OperatorKind.ARITHMETIC_ABS, False): BZOperator.FABS,
    (cpt.OperatorKind.PREVIOUS, True): BZOperator.PREV,
    (cpt.OperatorKind.PREVIOUS, False): BZOperator.PREV,
    (cpt.OperatorKind.ARITHMETIC_RATE, True): BZOperator.ISUB,
    (cpt.OperatorKind.ARITHMETIC_RATE, False): BZOperator.FSUB,
    (cpt.OperatorKind.EQUAL, True): BZOperator.IEQ,
    (cpt.OperatorKind.EQUAL, False): BZOperator.FEQ,
    (cpt.OperatorKind.NOT_EQUAL, True): BZOperator.INEQ,
    (cpt.OperatorKind.NOT_EQUAL, False): BZOperator.FNEQ,
    (cpt.OperatorKind.GREATER_THAN, True): BZOperator.IGT,
    (cpt.OperatorKind.GREATER_THAN, False): BZOperator.FGT,
    (cpt.OperatorKind.GREATER_THAN_OR_EQUAL, True): BZOperator.IGTE,
    (cpt.OperatorKind.GREATER_THAN_OR_EQUAL, False): BZOperator.FGTE,
    (cpt.OperatorKind.LESS_THAN, True): BZOperator.ILT,
    (cpt.OperatorKind.LESS_THAN, False): BZOperator.FLT,
    (cpt.OperatorKind.LESS_THAN_OR_EQUAL, True): BZOperator.ILTE,
    (cpt.OperatorKind.LESS_THAN_OR_EQUAL, False): BZOperator.FLTE,
}


class ATRelOp(Enum):
    EQ = 0b000
    NEQ = 0b001
    LT = 0b010
    LEQ = 0b011
    GT = 0b100
    GEQ = 0b101
    NONE = 0b111

    def __str__(self) -> str:
        return self.name.lower()


AT_REL_OP_MAP = {
    cpt.OperatorKind.EQUAL: ATRelOp.EQ,
    cpt.OperatorKind.NOT_EQUAL: ATRelOp.NEQ,
    cpt.OperatorKind.LESS_THAN: ATRelOp.LT,
    cpt.OperatorKind.LESS_THAN_OR_EQUAL: ATRelOp.LEQ,
    cpt.OperatorKind.GREATER_THAN: ATRelOp.GT,
    cpt.OperatorKind.GREATER_THAN_OR_EQUAL: ATRelOp.GEQ,
}


class ATFilter(Enum):
    NONE = 0b0000
    BOOL = 0b0001
    INT = 0b0010
    FLOAT = 0b0011
    FORMULA = 0b0100
    # EXACTLY_ONE_OF = 0b1000
    # NONE_OF        = 0b1001
    # ALL_OF         = 0b1010

    def __str__(self) -> str:
        return self.name.lower()


AT_FILTER_MAP = {
    types.BoolType: ATFilter.BOOL,
    types.IntType: ATFilter.INT,
    types.FloatType: ATFilter.FLOAT,
}


class TLOperandType(Enum):
    DIRECT = 0b01
    ATOMIC = 0b00
    SUBFORMULA = 0b10
    NONE = 0b11


TL_OPERAND_TYPE_MAP = {
    cpt.Constant: TLOperandType.DIRECT,
    cpt.AtomicChecker: TLOperandType.ATOMIC,
}


class FTOperator(Enum):
    # See monitors/static_c/src/engines/mltl/mltl.h
    NOP = 0b11111
    CONFIG = 0b11110
    LOAD = 0b11101
    RETURN = 0b11100
    EVENTUALLY = 0b11011
    GLOBAL = 0b11010
    UNTIL = 0b11001
    RELEASE = 0b11000
    NOT = 0b10111
    AND = 0b10110
    OR = 0b10101
    IMPLIES = 0b10100
    EQUIV = 0b10000
    XOR = 0b10001

    def is_temporal(self) -> bool:
        return self is FTOperator.GLOBAL or self is FTOperator.UNTIL

    def is_load(self) -> bool:
        return self is FTOperator.LOAD

    def __str__(self) -> str:
        return self.name.lower()


FT_OPERATOR_MAP = {
    cpt.OperatorKind.GLOBAL: FTOperator.GLOBAL,
    cpt.OperatorKind.FUTURE: FTOperator.EVENTUALLY,
    cpt.OperatorKind.UNTIL: FTOperator.UNTIL,
    cpt.OperatorKind.RELEASE: FTOperator.RELEASE,
    cpt.OperatorKind.LOGICAL_NEGATE: FTOperator.NOT,
    cpt.OperatorKind.LOGICAL_AND: FTOperator.AND,
    cpt.OperatorKind.LOGICAL_OR: FTOperator.OR,
    cpt.OperatorKind.LOGICAL_IMPLIES: FTOperator.IMPLIES,
    cpt.OperatorKind.LOGICAL_EQUIV: FTOperator.EQUIV,
    cpt.OperatorKind.LOGICAL_XOR: FTOperator.XOR,
}


class PTOperator(Enum):
    NOP = 0b11111
    CONFIG = 0b11110
    LOAD = 0b11101
    RETURN = 0b11100
    ONCE = 0b01011
    HIST = 0b01010
    SINCE = 0b01001
    TRIGGER = 0b01000
    NOT = 0b10111
    AND = 0b10110
    OR = 0b10101
    IMPLIES = 0b10100
    EQUIV = 0b10000
    XOR = 0b10001

    def is_temporal(self) -> bool:
        return (
            self == PTOperator.ONCE
            or self == PTOperator.HIST
            or self == PTOperator.SINCE
            or self == PTOperator.TRIGGER
        )

    def is_load(self) -> bool:
        return self is PTOperator.LOAD

    def __str__(self) -> str:
        return self.name.lower()


PT_OPERATOR_MAP = {
    cpt.OperatorKind.ONCE: PTOperator.ONCE,
    cpt.OperatorKind.HISTORICAL: PTOperator.HIST,
    cpt.OperatorKind.SINCE: PTOperator.SINCE,
    cpt.OperatorKind.TRIGGER: PTOperator.TRIGGER,
    cpt.OperatorKind.LOGICAL_NEGATE: PTOperator.NOT,
    cpt.OperatorKind.LOGICAL_AND: PTOperator.AND,
    cpt.OperatorKind.LOGICAL_OR: PTOperator.OR,
    cpt.OperatorKind.LOGICAL_IMPLIES: PTOperator.IMPLIES,
    cpt.OperatorKind.LOGICAL_EQUIV: PTOperator.EQUIV,
    cpt.OperatorKind.LOGICAL_XOR: PTOperator.XOR,
    Any: PTOperator.NOP,
}

Operator = Union[FTOperator, PTOperator, BZOperator]
TLOperator = Union[FTOperator, PTOperator]


class CGType(Enum):
    DUOQ = 0
    TEMP = 1

    def __str__(self) -> str:
        return self.name


class AliasType(Enum):
    FORMULA = "F"
    CONTRACT = "C"

    def __str__(self) -> str:
        return self.name


class FieldType(Enum):
    ENGINE_TAG = 0
    INSTR_SIZE = 1
    BZ_ID = 2
    BZ_OPERATOR = 3
    BZ_OPERAND_ID = 5
    BZ_OPERAND_INT = 6
    BZ_OPERAND_FLOAT = 7
    AT_VALUE = 8
    AT_SIGNAL = 9
    # AT_VALUE_BOOL    = 8
    # AT_VALUE_SIG     = 9
    # AT_VALUE_INT     = 10
    # AT_VALUE_FLOAT   = 11
    AT_REL_OP = 12
    AT_FILTER = 13
    AT_ID = 14
    AT_COMPARE_VALUE_IS_SIGNAL = 15
    TL_ID = 16
    TL_OPERATOR = 17
    TL_OPERAND_TYPE = 18
    TL_OPERAND_VALUE = 19


field_format_str_map = {
    FieldType.ENGINE_TAG: "B",
    FieldType.INSTR_SIZE: "B",
    FieldType.BZ_ID: "I",
    FieldType.BZ_OPERAND_ID: "Ixxxx",
    FieldType.BZ_OPERAND_INT: "ixxxx",
    FieldType.BZ_OPERAND_FLOAT: "d",
    FieldType.BZ_OPERATOR: "B",
    FieldType.AT_VALUE: "8s",
    # FieldType.AT_VALUE_BOOL:    "?xxxxxxx",
    FieldType.AT_SIGNAL: "B",
    # FieldType.AT_VALUE_INT:     "q",
    # FieldType.AT_VALUE_FLOAT:   "d",
    FieldType.AT_REL_OP: "i",
    FieldType.AT_FILTER: "i",
    FieldType.AT_ID: "B",
    FieldType.AT_COMPARE_VALUE_IS_SIGNAL: "B",
    FieldType.TL_ID: "I",
    FieldType.TL_OPERATOR: "B",
    FieldType.TL_OPERAND_TYPE: "B",
    FieldType.TL_OPERAND_VALUE: "I",
}


@dataclass
class ATInstruction:
    engine_tag: EngineTag
    id: int
    relational_operator: ATRelOp
    signal_id: int
    signal_type: ATFilter
    compare_value: Union[bool, int, float]
    compare_is_signal: bool
    atomic_id: int

    def __str__(self) -> str:
        field_strs: list[str] = []

        field_strs.append(f"{self.engine_tag.name}")
        field_strs.append(f"a{self.id:<2}")
        field_strs.append(f"{self.relational_operator:3}")
        field_strs.append(f"s{self.signal_id}")
        field_strs.append(
            f"{str(self.signal_type) + '(' + ('s' if self.compare_is_signal else '') + str(self.compare_value) + ')':10}"
        )

        return " ".join(field_strs)


@dataclass
class BZInstruction:
    engine_tag: EngineTag
    id: int
    operator: BZOperator
    operand1: Union[None, int, float]
    operand2: int

    def __str__(self) -> str:
        field_strs: list[str] = []

        field_strs.append(f"{self.engine_tag.name}")
        field_strs.append(f"b{self.id:<2}")
        field_strs.append(f"{self.operator:6}")
        if self.operand1 is not None:
            field_strs.append(f"{self.operand1}")
        if self.operand2 is not None:
            field_strs.append(f"{self.operand2}")

        return " ".join(field_strs)


@dataclass
class TLInstruction:
    engine_tag: EngineTag
    id: int
    operator: TLOperator
    operand1_type: TLOperandType
    operand1_value: Any
    operand2_type: TLOperandType
    operand2_value: Any

    def __str__(self) -> str:
        field_strs: list[str] = []

        field_strs.append(f"{self.engine_tag.name}")
        if isinstance(self.operator, PTOperator) and self.operator.is_temporal():
            field_strs.append(f"q{self.id:<2}")
        else:
            field_strs.append(f"n{self.id:<2}")
        field_strs.append(f"{self.operator:6}")

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
class CGInstruction:
    engine_tag: EngineTag
    type: CGType
    instruction: TLInstruction

    def __str__(self) -> str:
        field_strs: list[str] = [f"{self.engine_tag.name}"]
        field_strs.append(f"{self.instruction.engine_tag}")
        field_strs.append(f"{self.type:3}")
        if self.type == CGType.DUOQ:
            field_strs.append(f"q{self.instruction.id}")
            field_strs.append(f"|{self.instruction.operand1_value}|")
            if self.instruction.operand2_type == TLOperandType.ATOMIC:
                field_strs.append(f"<{self.instruction.operand2_value}>")
        elif self.type == CGType.TEMP:
            field_strs.append(f"q{self.instruction.id}")
            field_strs.append(f"[{self.instruction.operand1_value}, "
                              f"{self.instruction.operand2_value}]")
        else:
            field_strs.append(f"n{self.instruction.operand1_value:<2}")
            field_strs.append(f"{self.instruction.id}")
        return " ".join(field_strs)


@dataclass
class AliasInstruction:
    type: AliasType
    symbol: str
    args: list[str]

    def __str__(self) -> str:
        return f"{self.type.value} {self.symbol} {' '.join(self.args)}"


Instruction = Union[ATInstruction, BZInstruction, TLInstruction, CGInstruction]


def gen_at_instruction(node: cpt.Expression, context: cpt.Context) -> ATInstruction:
    expr = context.atomic_checkers[node.symbol]

    # we can do the following since it is type-correct
    expr = cast(cpt.Operator, expr)
    signal = cast(cpt.Signal, expr.children[0])

    rhs = expr.children[1]
    if isinstance(rhs, cpt.Constant):
        compare_value = rhs.value  # type: ignore
    elif isinstance(rhs, cpt.Signal):
        compare_value = rhs.signal_id
    else:
        log.internal(
            MODULE_CODE,
            f"Compare value for AT checker must be a constant or signal, got '{type(rhs)}' ({rhs})."
            "\n\tWhy did this get past the type checker?",
        )
        compare_value = 0

    if node in context.atomic_id:
        aid = context.atomic_id[node]
    else:
        log.internal(MODULE_CODE, f"No atomic ID assigned for '{node}'")
        aid = -1

    return ATInstruction(
        EngineTag.AT,
        aid,
        AT_REL_OP_MAP[expr.operator],
        signal.signal_id,
        AT_FILTER_MAP[type(signal.type)],  # type: ignore
        compare_value,
        isinstance(expr.children[1], cpt.Signal),
        aid,
    )


def gen_bz_instruction(
    expr: cpt.Expression,
    context: cpt.Context,
    instructions: dict[cpt.Expression, BZInstruction],
) -> BZInstruction:
    bzid = len(instructions)

    if isinstance(expr, cpt.Signal):
        operand1 = expr.signal_id
        operand2 = 0
        if types.is_integer_type(expr.type):
            operator = BZOperator.ILOAD
        else:
            operator = BZOperator.FLOAD

    elif isinstance(expr, cpt.Constant) and types.is_integer_type(expr.type):
        operand1 = expr.value
        operand2 = 0
        operator = BZOperator.ICONST
    elif isinstance(expr, cpt.Constant):
        operand1 = expr.value
        operand2 = 0
        operator = BZOperator.FCONST
    elif isinstance(expr, cpt.Atomic):
        operand1 = instructions[expr.children[0]].id
        operand2 = 0 if expr not in context.atomic_id else context.atomic_id[expr]
        operator = BZOperator.STORE
    elif len(expr.children) == 1:
        operand1 = instructions[expr.children[0]].id
        operand2 = 0

        is_int_operator = types.is_integer_type(expr.type)
        expr = cast(cpt.Operator, expr)

        # Special case: cpt.OperatorKind.ARITHMETIC_NEGATE and cpt.OperatorKind.ARITHMETIC_SUBTRACT have the same symbol,
        # so we need to catch this here
        if expr.operator is cpt.OperatorKind.ARITHMETIC_NEGATE:
            operator = BZOperator.INEG if is_int_operator else BZOperator.FNEG
        else:
            operator = BZ_OPERATOR_MAP[(expr.operator, is_int_operator)]
    elif len(expr.children) == 2:
        operand1 = instructions[expr.children[0]].id
        operand2 = instructions[expr.children[1]].id

        if cpt.is_relational_operator(expr):
            is_int_operator = types.is_integer_type(expr.children[0].type)
        else:
            is_int_operator = types.is_integer_type(expr.type)

        expr = cast(cpt.Operator, expr)
        operator = BZ_OPERATOR_MAP[(expr.operator, is_int_operator)]
    else:
        operand1 = 0
        operand2 = 0

        is_int_operator = types.is_integer_type(expr.type)
        expr = cast(cpt.Operator, expr)
        operator = BZ_OPERATOR_MAP[(expr.operator, is_int_operator)]

    bz_instr = BZInstruction(
        EngineTag.BZ,
        bzid,
        operator,
        operand1,
        operand2,
    )

    log.debug(MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{bz_instr}")

    return bz_instr


def gen_tl_operand(
    operand: Optional[cpt.Node], instructions: dict[cpt.Expression, TLInstruction]
) -> tuple[TLOperandType, Any]:
    if isinstance(operand, cpt.Constant):
        operand_type = TLOperandType.DIRECT
        operand_value = operand.value
    elif operand in instructions:
        operand_type = TLOperandType.SUBFORMULA
        operand_value = instructions[operand].id
    else:
        operand_type = TLOperandType.NONE
        operand_value = 0

    return (operand_type, operand_value)


def gen_ft_instruction(
    expr: cpt.Expression, instructions: dict[cpt.Expression, TLInstruction]
) -> Optional[TLInstruction]:
    ftid = len(instructions)

    if isinstance(expr, cpt.Formula):
        operand1_type, operand1_value = (
            TLOperandType.SUBFORMULA,
            instructions[expr.get_expr()].id,
        )
        operand2_type, operand2_value = (TLOperandType.DIRECT, expr.formula_number)
        operator = FTOperator.RETURN
    elif len(expr.children) == 0:
        operand1_type, operand1_value = gen_tl_operand(None, instructions)
        operand2_type, operand2_value = gen_tl_operand(None, instructions)

        expr = cast(cpt.Operator, expr)
        operator = FT_OPERATOR_MAP[expr.operator]
    elif len(expr.children) == 1:
        operand1_type, operand1_value = gen_tl_operand(expr.children[0], instructions)
        operand2_type, operand2_value = gen_tl_operand(None, instructions)

        expr = cast(cpt.Operator, expr)
        operator = FT_OPERATOR_MAP[expr.operator]
    elif len(expr.children) == 2:
        operand1_type, operand1_value = gen_tl_operand(expr.children[0], instructions)
        operand2_type, operand2_value = gen_tl_operand(expr.children[1], instructions)

        expr = cast(cpt.Operator, expr)
        operator = FT_OPERATOR_MAP[expr.operator]
    else:
        log.error(
            MODULE_CODE,
            "Trying to assemble operator with more than 2 arguments. "
            "Did you enable an optimization incompatible with R2U2?\n\t"
            f"{expr}"
        )
        return None

    ft_instr = TLInstruction(
        EngineTag.TL,
        ftid,
        operator,
        operand1_type,
        operand1_value,
        operand2_type,
        operand2_value,
    )

    log.debug(MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{ft_instr}")

    return ft_instr


def gen_pt_instruction(
    expr: cpt.Expression, instructions: dict[cpt.Expression, TLInstruction], offset: int
) -> Optional[TLInstruction]:
    ptid = len(instructions)

    if isinstance(expr, cpt.Formula):
        operand1_type, operand1_value = (
            TLOperandType.SUBFORMULA,
            instructions[expr.get_expr()].id,
        )
        operand2_type, operand2_value = (TLOperandType.DIRECT, expr.formula_number)
        operator = PTOperator.RETURN
    elif len(expr.children) == 0:
        operand1_type, operand1_value = gen_tl_operand(None, instructions)
        operand2_type, operand2_value = gen_tl_operand(None, instructions)

        expr = cast(cpt.Operator, expr)
        operator = PT_OPERATOR_MAP[expr.operator]
    elif len(expr.children) == 1:
        operand1_type, operand1_value = gen_tl_operand(expr.children[0], instructions)
        operand2_type, operand2_value = gen_tl_operand(None, instructions)

        expr = cast(cpt.Operator, expr)
        operator = PT_OPERATOR_MAP[expr.operator]
    elif len(expr.children) == 2:
        operand1_type, operand1_value = gen_tl_operand(expr.children[0], instructions)
        operand2_type, operand2_value = gen_tl_operand(expr.children[1], instructions)

        expr = cast(cpt.Operator, expr)
        operator = PT_OPERATOR_MAP[expr.operator]
    else:
        log.error(
            MODULE_CODE,
            "Trying to assemble operator with more than 2 arguments. "
            "Did you enable an optimization incompatible with R2U2?\n\t"
            f"{expr}"
        )
        return None

    pt_instr = TLInstruction(
        EngineTag.TL,
        ptid + offset,
        operator,
        operand1_type,
        operand1_value,
        operand2_type,
        operand2_value,
    )

    log.debug(MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{pt_instr}")

    return pt_instr


def gen_ft_duoq_instructions(
    expr: cpt.Expression, instructions: dict[cpt.Expression, TLInstruction]
) -> list[CGInstruction]:

    # Propositional operators only need simple queues
    if not isinstance(expr, cpt.TemporalOperator):
        cg_duoq = CGInstruction(
            EngineTag.CG,
            CGType.DUOQ,
            TLInstruction(
                EngineTag.TL,
                instructions[expr].id,
                FTOperator.CONFIG,
                TLOperandType.ATOMIC,
                expr.scq[1] - expr.scq[0],
                TLOperandType.NONE,
                0,
            ),
        )
        log.debug(MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{cg_duoq}")
        return [cg_duoq]

    # Temporal operators need to reserve queue length for temporal parameter
    # blocks, and emit an additional configuration instruction
    cg_duoq = CGInstruction(
        EngineTag.CG,
        CGType.DUOQ,
        TLInstruction(
            EngineTag.TL,
            instructions[expr].id,
            FTOperator.CONFIG,
            TLOperandType.ATOMIC,
            # TODO: Move magic number (size of temporal block)
            (expr.scq[1] - expr.scq[0]) + 4,
            TLOperandType.NONE,
            0,
        ),
    )

    cg_temp = CGInstruction(
        EngineTag.CG,
        CGType.TEMP,
        TLInstruction(
            EngineTag.TL,
            instructions[expr].id,
            FTOperator.CONFIG,
            TLOperandType.SUBFORMULA,
            expr.interval.lb,
            TLOperandType.SUBFORMULA,
            expr.interval.ub,
        ),
    )

    log.debug(
        MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{cg_duoq}\n\t" f"{cg_temp}"
    )

    return [cg_duoq, cg_temp]


def gen_pt_duoq_instructions(
    expr: cpt.Expression, instructions: dict[cpt.Expression, TLInstruction]
) -> list[CGInstruction]:
    # Propositional operators only need simple queues
    if not isinstance(expr, cpt.TemporalOperator):
        cg_duoq = CGInstruction(
            EngineTag.CG,
            CGType.DUOQ,
            TLInstruction(
                EngineTag.TL,
                instructions[expr].id,
                PTOperator.CONFIG,
                TLOperandType.ATOMIC,
                (expr.scq[1] - expr.scq[0]),
                TLOperandType.NONE,
                0,
            ),
        )
        log.debug(MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{cg_duoq}")
        return [cg_duoq]

    # Temporal operators need to reserve queue length for temporal parameter
    # blocks, and emit an additional configuration instruction
    cg_duoq = CGInstruction(
        EngineTag.CG,
        CGType.DUOQ,
        TLInstruction(
            EngineTag.TL,
            instructions[expr].id,
            PTOperator.CONFIG,
            TLOperandType.ATOMIC,
            # TODO: Move magic number (size of temporal block)
            (expr.scq[1] - expr.scq[0]) + 4,
            TLOperandType.NONE,
            0,
        ),
    )

    cg_temp = CGInstruction(
        EngineTag.CG,
        CGType.TEMP,
        TLInstruction(
            EngineTag.TL,
            instructions[expr].id,
            PTOperator.CONFIG,
            TLOperandType.SUBFORMULA,
            expr.interval.lb,
            TLOperandType.SUBFORMULA,
            expr.interval.ub,
        ),
    )

    log.debug(
        MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{cg_duoq}\n\t" f"{cg_temp}"
    )

    return [cg_duoq, cg_temp]


def gen_assembly(program: cpt.Program, context: cpt.Context) -> Optional[list[Instruction]]:
    at_instructions: dict[cpt.Expression, ATInstruction] = {}
    bz_instructions: dict[cpt.Expression, BZInstruction] = {}
    ft_instructions: dict[cpt.Expression, TLInstruction] = {}
    pt_instructions: dict[cpt.Expression, TLInstruction] = {}
    cg_instructions: dict[cpt.Expression, list[CGInstruction]] = {}

    # For tracking duoq usage across FT and PT
    ft_duoqs: int = 0

    log.debug(MODULE_CODE, 1, f"Generating assembly for program:\n{program}")

    for expr in cpt.postorder(program.ft_spec_set, context):
        if expr == program.ft_spec_set:
            continue

        if expr in context.atomic_id:
            ftid = len(ft_instructions)
            ft_instructions[expr] = TLInstruction(
                EngineTag.TL,
                ftid,
                FTOperator.LOAD,
                TLOperandType.ATOMIC,
                context.atomic_id[expr],
                TLOperandType.NONE,
                0,
            )

            log.debug(MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{ft_instructions[expr]}")
            cg_instructions[expr] = gen_ft_duoq_instructions(expr, ft_instructions)
            ft_duoqs += 1

        # Special case for bool -- TL ops directly embed bool literals in their operands,
        # so if this is a bool literal with only TL parents we should skip.
        # TODO: Is there a case where a bool is used by the BZ engine? As in when this is ever not true for a bool?
        if isinstance(expr, cpt.Constant) and expr.has_only_tl_parents():
            continue

        if expr.engine == types.R2U2Engine.ATOMIC_CHECKER:
            at_instructions[expr] = gen_at_instruction(expr, context)
        elif expr.engine == types.R2U2Engine.BOOLEANIZER:
            bz_instructions[expr] = gen_bz_instruction(expr, context, bz_instructions)
        elif expr.engine == types.R2U2Engine.TEMPORAL_LOGIC:
            new_ft_instruction = gen_ft_instruction(expr, ft_instructions)
            if not new_ft_instruction:
                return None
            ft_instructions[expr] = new_ft_instruction
            cg_instructions[expr] = gen_ft_duoq_instructions(expr, ft_instructions)
            ft_duoqs += 1

    for expr in cpt.postorder(program.pt_spec_set, context):
        if expr == program.pt_spec_set:
            continue

        if expr in context.atomic_id:
            ptid = len(pt_instructions)
            pt_instructions[expr] = TLInstruction(
                EngineTag.TL,
                ptid + ft_duoqs,
                PTOperator.LOAD,
                TLOperandType.ATOMIC,
                context.atomic_id[expr],
                TLOperandType.NONE,
                0,
            )
            log.debug(MODULE_CODE, 1, f"Generating: {expr}\n\t" f"{pt_instructions[expr]}")
            cg_instructions[expr] = gen_pt_duoq_instructions(expr, pt_instructions)

        if expr.engine == types.R2U2Engine.ATOMIC_CHECKER:
            at_instructions[expr] = gen_at_instruction(expr, context)
        elif expr.engine == types.R2U2Engine.BOOLEANIZER:
            bz_instructions[expr] = gen_bz_instruction(expr, context, bz_instructions)
        elif expr.engine == types.R2U2Engine.TEMPORAL_LOGIC:
            new_pt_instruction = gen_pt_instruction(expr, pt_instructions, ft_duoqs)
            if not new_pt_instruction:
                return None
            pt_instructions[expr] = new_pt_instruction
            cg_instructions[expr] = gen_pt_duoq_instructions(expr, pt_instructions)

    # Move all PREV booleanizer instructions to the end (i.e., always update the 'previous' 
    # value after current iteration)
    for key in list(bz_instructions):
        if bz_instructions[key].operator is BZOperator.PREV:
            bz_instructions[key] = bz_instructions.pop(key)

    return (
        list(at_instructions.values())
        + list(bz_instructions.values())
        + list(ft_instructions.values())
        + list(pt_instructions.values())
        + [cg_instr for cg_instrs in cg_instructions.values() for cg_instr in cg_instrs]
    )


def pack_at_instruction(
    instruction: ATInstruction,
    format_strs: dict[FieldType, str],
) -> bytes:
    binary = bytes()

    if instruction.compare_is_signal:
        compare_format_str = "Bxxxxxxx"
    elif isinstance(instruction.compare_value, bool):
        compare_format_str = "?xxxxxxx"
    elif isinstance(instruction.compare_value, int):
        compare_format_str = "q"
    else:  # isinstance(instruction.compare_value, float):
        compare_format_str = "d"

    compare_bytes = CStruct(f"{ENDIAN}{compare_format_str}").pack(
        instruction.compare_value
    )

    format_str = ENDIAN
    format_str += format_strs[FieldType.AT_VALUE]
    format_str += format_strs[FieldType.AT_VALUE]
    format_str += format_strs[FieldType.AT_REL_OP]
    format_str += format_strs[FieldType.AT_FILTER]
    format_str += format_strs[FieldType.AT_SIGNAL]
    format_str += format_strs[FieldType.AT_ID]
    format_str += format_strs[FieldType.AT_COMPARE_VALUE_IS_SIGNAL]
    format_str += format_strs[FieldType.AT_ID]

    log.debug(
        MODULE_CODE, 1,
        f"Packing: {instruction}\n\t"
        f"{format_strs[FieldType.ENGINE_TAG]:2} "
        f"[{compare_format_str:<8}] "
        f"[xxxxxxxx] "
        f"{format_strs[FieldType.AT_REL_OP]:2} "
        f"{format_strs[FieldType.AT_FILTER]:2} "
        f"{format_strs[FieldType.AT_SIGNAL]:2} "
        f"{format_strs[FieldType.AT_ID]:2} "
        f"{format_strs[FieldType.AT_COMPARE_VALUE_IS_SIGNAL]:2} "
        f"{format_strs[FieldType.AT_ID]:2} "
        f"\n\t"
        f"{instruction.engine_tag.value:<2} "
        f"[{instruction.compare_value:<8}] "
        f"[        ] "
        f"{instruction.relational_operator.value:<2} "
        f"{instruction.signal_type.value:<2} "
        f"{instruction.signal_id:<2} "
        f"{instruction.atomic_id:<2} "
        f"{instruction.compare_is_signal:<2} "
        f"{instruction.atomic_id:<2} ",
    )

    engine_tag_binary = CStruct(f"{ENDIAN}{format_strs[FieldType.ENGINE_TAG]}").pack(
        instruction.engine_tag.value
    )

    binary = engine_tag_binary + CStruct(format_str).pack(
        compare_bytes,
        CStruct(f"{ENDIAN}xxxxxxxx").pack(),
        instruction.relational_operator.value,
        instruction.signal_type.value,
        instruction.signal_id,
        instruction.atomic_id,
        instruction.compare_is_signal,
        instruction.atomic_id,
    )

    return binary


def pack_bz_instruction(
    instruction: BZInstruction,
    format_strs: dict[FieldType, str],
) -> bytes:
    log.debug(
        MODULE_CODE, 1,
        f"Packing: {instruction}\n\t"
        f"{format_strs[FieldType.ENGINE_TAG]:2} "
        f"{format_strs[FieldType.BZ_OPERAND_FLOAT] if isinstance(instruction.operand1, float) else (format_strs[FieldType.BZ_OPERAND_ID] if (instruction.operator is BZOperator.ICONST) else format_strs[FieldType.BZ_OPERAND_INT])} "
        f"{format_strs[FieldType.BZ_ID]:2} "
        f"{format_strs[FieldType.BZ_ID]:2} "
        f"{format_strs[FieldType.BZ_OPERATOR]:2} "
        f"\n\t"
        f"{instruction.engine_tag.value:<2} "
        f"{instruction.operand1:<5} "
        f"{instruction.operand2:<2} "
        f"{instruction.id:<2} "
        f"{instruction.operator.value:<2} ",
    )

    binary = bytes()

    format_str = ENDIAN
    format_str += (
        format_strs[FieldType.BZ_OPERAND_FLOAT]
        if isinstance(instruction.operand1, float)
        else format_strs[FieldType.BZ_OPERAND_ID]
        if instruction.operator is BZOperator.ICONST
        else format_strs[FieldType.BZ_OPERAND_INT]
    )
    format_str += (
        format_strs[FieldType.BZ_ID]
    )
    format_str += format_strs[FieldType.BZ_ID]
    format_str += format_strs[FieldType.BZ_OPERATOR]

    engine_tag_binary = CStruct(f"{ENDIAN}{format_strs[FieldType.ENGINE_TAG]}").pack(
        instruction.engine_tag.value
    )

    binary = engine_tag_binary + CStruct(format_str).pack(
        instruction.operand1,
        instruction.operand2,
        instruction.id,
        instruction.operator.value,
    )

    return binary


def pack_tl_instruction(
    instruction: TLInstruction,
    format_strs: dict[FieldType, str],
) -> bytes:
    log.debug(
        MODULE_CODE, 1,
        f"Packing: {instruction}\n\t"
        f"{format_strs[FieldType.ENGINE_TAG]:2} "
        f"{format_strs[FieldType.TL_OPERAND_VALUE]:4} "
        f"{format_strs[FieldType.TL_OPERAND_VALUE]:4} "
        f"{format_strs[FieldType.TL_ID]:4} "
        f"{format_strs[FieldType.TL_OPERAND_TYPE]:2} "
        f"{format_strs[FieldType.TL_OPERAND_TYPE]:2} "
        f"{format_strs[FieldType.TL_OPERATOR]:2}"
        f"\n\t"
        f"{instruction.engine_tag.value:<2} "
        f"{instruction.operand1_value:<4} "
        f"{instruction.operand2_value:<4} "
        f"{instruction.id:<4} "
        f"{instruction.operand1_type.value:<2} "
        f"{instruction.operand2_type.value:<2} "
        f"{instruction.operator.value:<2}",
    )

    binary = bytes()

    format_str = ENDIAN
    format_str += format_strs[FieldType.TL_OPERAND_VALUE]
    format_str += format_strs[FieldType.TL_OPERAND_VALUE]
    format_str += format_strs[FieldType.TL_ID]
    format_str += format_strs[FieldType.TL_OPERAND_TYPE]
    format_str += format_strs[FieldType.TL_OPERAND_TYPE]
    format_str += format_strs[FieldType.TL_OPERATOR]

    engine_tag_binary = CStruct(f"{ENDIAN}{format_strs[FieldType.ENGINE_TAG]}").pack(
        instruction.engine_tag.value
    )

    binary = engine_tag_binary + CStruct(format_str).pack(
        instruction.operand1_value,
        instruction.operand2_value,
        instruction.id,
        instruction.operand1_type.value,
        instruction.operand2_type.value,
        instruction.operator.value,
    )

    return binary


def pack_cg_instruction(
    instruction: CGInstruction, 
    format_strs: dict[FieldType, str]
) -> bytes:
    log.debug(
        MODULE_CODE, 1,
        f"Packing: {instruction}\n\t"
        f"{format_strs[FieldType.ENGINE_TAG]:<2}"
        f"\n\t"
        f"{instruction.engine_tag.value:<2}",
    )

    binary = bytes()

    format_str = ENDIAN
    format_str += format_strs[FieldType.ENGINE_TAG]

    binary += CStruct(format_str).pack(instruction.engine_tag.value)

    binary += pack_tl_instruction(instruction.instruction, format_strs)

    return binary


def pack_instruction(
    instruction: Instruction,
    format_strs: dict[FieldType, str],
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
        log.error(MODULE_CODE, f"Invalid instruction type ({type(instruction)}).")
        binary = bytes()

    binary_len = CStruct(f"{ENDIAN}B").pack(len(binary) + 1)
    return binary_len + binary


def pack_aliases(program: cpt.Program, context: cpt.Context) -> tuple[list[AliasInstruction], bytes]:
    aliases: list[AliasInstruction] = []
    binary = bytes()

    for spec in program.get_specs():
        if not isinstance(spec, cpt.Formula):
            log.internal(
                "Contract found during assembly. Why didn't transform_contracts catch this?",
                MODULE_CODE,
            )
            continue

        alias = AliasInstruction(AliasType.FORMULA, spec.symbol, [str(spec.formula_number)])
        aliases.append(alias)
        binary += str(alias).encode("ascii") + b"\x00"

        log.debug(MODULE_CODE, 1, f"Packing: {alias}")

    for label, contract in context.contracts.items():
        alias = AliasInstruction(AliasType.CONTRACT, label, [str(f) for f in contract.formula_numbers])
        aliases.append(alias)
        binary += str(alias).encode("ascii") + b"\x00"

        log.debug(MODULE_CODE, 1, f"Packing: {alias}")

    return (aliases, binary)


def assemble(
    program: cpt.Program, context: cpt.Context, quiet: bool
) -> tuple[list[Union[Instruction, AliasInstruction]], bytes]:
    log.debug(MODULE_CODE, 1, "Assembling")

    check_sizes()
    assembly = gen_assembly(program, context)

    if not assembly:
        return ([], bytes())

    binary = bytes()
    binary_header = (
        f"C2PO Version 1.0.0 for R2U2 V3.1 - BOM: {ENDIAN}".encode("ascii") + b"\x00"
    )
    binary += CStruct("B").pack(len(binary_header) + 1) + binary_header

    for instr in assembly:
        binary += pack_instruction(instr, field_format_str_map)

    binary += b"\x00"

    (aliases, binary_aliases) = pack_aliases(program, context)
    assembly += aliases
    binary += binary_aliases

    binary += b"\x00"

    return (assembly, binary)
