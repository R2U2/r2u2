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
    TEMPORAL_LOGIC = 0
    BOOLEANIZER = 1
    ATOMIC_CHECKER = 2


class Interval(NamedTuple):
    lb: int
    ub: int


SignalMapping = Dict[str, int]


class BaseType(enum.Enum):
    NOTYPE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3
    SET = 4
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


class SetType(Type):
    """Parameterized set C2PO type."""

    def __init__(self, member_type: Type, is_const: bool = False):
        super().__init__(BaseType.SET, is_const, "set<" + str(member_type) + ">")
        self.member_type: Type = member_type

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            if isinstance(arg, SetType):
                return self.member_type.__eq__(arg.member_type)
        return False

    def __str__(self) -> str:
        return f"set<{self.member_type}>"


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


def is_set_type(t: Type) -> bool:
    return isinstance(t, SetType)


def set_types(
    impl: R2U2Implementation, int_width: int, int_signed: bool, float_width: int
):
    """Check for valid int and float widths and configure program types accordingly."""
    IntType.is_signed = int_signed

    if int_width < 1:
        log.error("Invalid int width, must be greater than 0", MODULE_CODE)

    if float_width < 1:
        log.error("Invalid float_width width, must be greater than 0", MODULE_CODE)

    if int_width % 8 != 0:
        log.error(
            " Invalid int width, must be a multiple of 8 for byte-alignment.",
            MODULE_CODE,
        )

    if float_width % 8 != 0:
        log.error(
            " Invalid float width, must be a multiple of 8 for byte-alignment.",
            MODULE_CODE,
        )

    if impl == R2U2Implementation.C or impl == R2U2Implementation.CPP:
        if int_width == 8 or int_width == 16 or int_width == 32 or int_width == 64:
            IntType.width = int_width
        else:
            log.error(
                " Invalid int width, must correspond to a C standard int width (8, 16, 32, or 64).",
                MODULE_CODE,
            )

        if float_width == 32 or float_width == 64:
            FloatType.width = float_width
        else:
            log.error(
                " Invalid float width, must correspond to a C standard float width (32 or 64).",
                MODULE_CODE,
            )
    else:
        IntType.width = int_width
        FloatType.width = float_width
