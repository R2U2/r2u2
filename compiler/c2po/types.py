from typing import NamedTuple, Dict
from enum import Enum

from c2po import log


class R2U2Implementation(Enum):
    C = 0
    CPP = 1
    VHDL = 2


class R2U2Engine(Enum):
    NONE = 0
    TEMPORAL_LOGIC = 0
    BOOLEANIZER = 1
    ATOMIC_CHECKER = 2


class Interval(NamedTuple):
    lb: int
    ub: int


SignalMapping = Dict[str, int]


def str_to_r2u2_implementation(s: str) -> R2U2Implementation:
    if s.lower() == "c":
        return R2U2Implementation.C
    elif s.lower() == "c++" or s.lower() == "cpp":
        return R2U2Implementation.CPP
    elif s.lower() == "fpga" or s.lower() == "vhdl":
        return R2U2Implementation.VHDL
    else:
        log.logger.error(f" R2U2 implementation '{s}' unsupported. Defaulting to C.")
        return R2U2Implementation.C


class BaseType(Enum):
    NOTYPE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3
    SET = 4
    STRUCT = 5


class Type:
    """Abstract base class representing a C2PO type."""

    def __init__(self, type: BaseType, is_const: bool, name: str):
        self.value: BaseType = type
        self.name: str = name
        self.is_const: bool = is_const

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, Type):
            return self.value == arg.value
        return False

    def __str__(self) -> str:
        return self.name


class NoType(Type):
    """An invalid C2PO type."""

    def __init__(self):
        super().__init__(BaseType.NOTYPE, True, "NoType")


class BoolType(Type):
    """Boolean C2PO type."""

    def __init__(self, is_const: bool):
        super().__init__(BaseType.BOOL, is_const, "bool")


class IntType(Type):
    """Integer C2PO type with configurable width and signedness."""

    width: int = 8
    is_signed: bool = False

    def __init__(self, is_const: bool):
        super().__init__(BaseType.INT, is_const, "int")


class FloatType(Type):
    """Floating point C2PO type with configurable width."""

    width: int = 32

    def __init__(self, is_const: bool):
        super().__init__(BaseType.FLOAT, is_const, "float")


class StructType(Type):
    """Structured date C2PO type represented via a name."""

    def __init__(self, is_const: bool, n: str):
        super().__init__(BaseType.STRUCT, is_const, n)
        self.name = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, StructType):
            return self.name == arg.name
        return False


class SetType(Type):
    """Parameterized set C2PO type."""

    def __init__(self, is_const: bool, m: Type):
        super().__init__(BaseType.SET, is_const, "set<" + str(m) + ">")
        self.member_type: Type = m

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            if isinstance(arg, SetType):
                return self.member_type.__eq__(arg.member_type)
        return False


def is_integer_type(t: Type) -> bool:
    return isinstance(t, IntType) or isinstance(t, BoolType)


def is_float_type(t: Type) -> bool:
    return isinstance(t, FloatType)


def set_types(
    impl: R2U2Implementation, int_width: int, int_signed: bool, float_width: int
):
    """Check for valid int and float widths and configure program types accordingly."""
    IntType.is_signed = int_signed

    if int_width < 1:
        log.logger.error(" Invalid int width, must be greater than 0")

    if float_width < 1:
        log.logger.error(" Invalid float_width width, must be greater than 0")

    if int_width % 8 != 0:
        log.logger.error(
            " Invalid int width, must be a multiple of 8 for byte-alignment."
        )

    if float_width % 8 != 0:
        log.logger.error(
            " Invalid float width, must be a multiple of 8 for byte-alignment."
        )

    if impl == R2U2Implementation.C or impl == R2U2Implementation.CPP:
        if int_width == 8 or int_width == 16 or int_width == 32 or int_width == 64:
            IntType.width = int_width
        else:
            log.logger.error(
                " Invalid int width, must correspond to a C standard int width (8, 16, 32, or 64)."
            )

        if float_width == 32 or float_width == 64:
            FloatType.width = float_width
        else:
            log.logger.error(
                " Invalid float width, must correspond to a C standard float width (32 or 64)."
            )
    else:
        IntType.width = int_width
        FloatType.width = float_width
