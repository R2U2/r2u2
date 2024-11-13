import enum
from typing import Dict, NamedTuple, Optional

from c2po import log

MODULE_CODE = "TYPE"


class R2U2Implementation(enum.Enum):
    C = 0
    CPP = 1
    VHDL = 2


class R2U2Engine(enum.Enum):
    NONE = 0
    SYSTEM = 1
    CONFIG = 2
    ATOMIC_CHECKER = 3
    TEMPORAL_LOGIC = 4
    BOOLEANIZER = 5


class Interval(NamedTuple):
    lb: int
    ub: int

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, Interval) and self.lb == __value.lb and self.ub == __value.ub


SignalMapping = Dict[str, int]


class BaseType(enum.Enum):
    NOTYPE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3
    ARRAY = 4
    STRUCT = 5
    CONTRACT = 6


class Type:
    """Abstract base class representing a C2PO type."""

    def __init__(self, type: BaseType, is_const: bool, symbol: str):
        self.value: BaseType = type
        self.symbol: str = symbol
        self.is_const: bool = is_const

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, Type):
            return self.value == arg.value
        return False

    def __hash__(self) -> int:
        return hash(self.value)

    def __str__(self) -> str:
        return self.symbol


class NoType(Type):
    """An invalid C2PO type."""

    def __init__(self):
        super().__init__(BaseType.NOTYPE, True, "NoType")


class BoolType(Type):
    """Boolean C2PO type."""

    def __init__(self, is_const: bool = False):
        super().__init__(BaseType.BOOL, is_const, "bool")


class IntType(Type):
    """Integer C2PO type with configurable width and signedness."""

    width: int = 8
    is_signed: bool = False

    def __init__(self, is_const: bool = False):
        super().__init__(BaseType.INT, is_const, "int")


class FloatType(Type):
    """Floating point C2PO type with configurable width."""

    width: int = 32

    def __init__(self, is_const: bool = False):
        super().__init__(BaseType.FLOAT, is_const, "float")


class StructType(Type):
    """Structured date C2PO type represented via a name."""

    def __init__(self, symbol: str, is_const: bool = False):
        super().__init__(BaseType.STRUCT, is_const, symbol)

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, StructType):
            return self.symbol == arg.symbol
        return False


class ContractValueType(Type):
    """Output value of Assume-Guarantee Contracts. Can be one of: inactive, invalid, or verified."""

    def __init__(self, is_const: bool = False):
        super().__init__(BaseType.CONTRACT, is_const, "contract")


class ArrayType(Type):
    """Array C2PO type."""

    def __init__(self, member_type: Type, is_const: bool = False, size: int = -1):
        super().__init__(BaseType.ARRAY, is_const, f"{member_type}[]")
        self.member_type: Type = member_type
        self.size: int = size

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, ArrayType):
            if not self.member_type.__eq__(arg.member_type):
                return False
            if self.size > -1 and arg.size > -1 and self.size != arg.size:
                return False
            return True
        return False

    def __str__(self) -> str:
        if self.size >= 0:
            return f"{self.member_type}[{self.size}]"
        return f"{self.member_type}[]"
    

def is_bool_type(t: Type) -> bool:
    return isinstance(t, BoolType)


def is_integer_type(t: Type) -> bool:
    return isinstance(t, IntType) or isinstance(t, BoolType)


def is_float_type(t: Type) -> bool:
    return isinstance(t, FloatType)


def is_struct_type(t: Type, symbol: Optional[str] = None) -> bool:
    """Returns true if `t` is a `StructType` and, if provided, has symbol `symbol`."""
    if symbol:
        return isinstance(t, StructType) and t.symbol == symbol
    return isinstance(t, StructType)


def is_array_type(t: Type) -> bool:
    return isinstance(t, ArrayType)


def configure_types(
    impl: R2U2Implementation, int_width: int, int_signed: bool, float_width: int
):
    """Check for valid int and float widths and configure program types accordingly."""
    IntType.is_signed = int_signed

    if int_width < 1:
        log.error(MODULE_CODE, "Invalid int width, must be greater than 0")

    if float_width < 1:
        log.error(MODULE_CODE, "Invalid float_width width, must be greater than 0")

    if int_width % 8 != 0:
        log.error(
            MODULE_CODE,
            " Invalid int width, must be a multiple of 8 for byte-alignment.",
        )

    if float_width % 8 != 0:
        log.error(
            MODULE_CODE,
            " Invalid float width, must be a multiple of 8 for byte-alignment.",
        )

    if impl == R2U2Implementation.C or impl == R2U2Implementation.CPP:
        if int_width == 8 or int_width == 16 or int_width == 32 or int_width == 64:
            IntType.width = int_width
        else:
            log.error(
                MODULE_CODE,
                " Invalid int width, must correspond to a C standard int width (8, 16, 32, or 64).",
            )

        if float_width == 32 or float_width == 64:
            FloatType.width = float_width
        else:
            log.error(
                MODULE_CODE,
                " Invalid float width, must correspond to a C standard float width (32 or 64).",
            )
    else:
        IntType.width = int_width
        FloatType.width = float_width
