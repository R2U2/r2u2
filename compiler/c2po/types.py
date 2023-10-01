from enum import Enum
from typing import NewType, NamedTuple, Union

from .logger import logger


class R2U2Implementation(Enum):
    C = 0
    CPP = 1
    VHDL = 2


class R2U2Engine(Enum):
    NONE = 0
    TEMPORAL_LOGIC = 0
    BOOLEANIZER = 1
    ATOMIC_CHECKER = 2

class MissionTime(int):
    pass

class Interval(NamedTuple):
    lb: int
    ub: Union[int, MissionTime]


def str_to_r2u2_implementation(s: str) -> R2U2Implementation:
    if s.lower() == "c":
        return R2U2Implementation.C
    elif s.lower() == "c++" or s.lower() == "cpp":
        return R2U2Implementation.CPP
    elif s.lower() == "fpga" or s.lower() == "vhdl":
        return R2U2Implementation.VHDL
    else:
        logger.error(f" R2U2 implementation '{s}' unsupported. Defaulting to C.")
        return R2U2Implementation.C


class C2POBaseType(Enum):
    NOTYPE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3
    SET = 4
    STRUCT = 5


class C2POType():
    """Abstract base class representing a C2PO type."""

    def __init__(self, t: C2POBaseType, c: bool, n: str):
        self.value: C2POBaseType = t
        self.name: str = n
        self.is_const: bool = c

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, C2POType):
            return self.value == arg.value
        return False

    def __str__(self) -> str:
        return self.name


class C2PONoType(C2POType):
    """An invalid C2PO type."""

    def __init__(self):
        super().__init__(C2POBaseType.NOTYPE, True, 'NoType')


class C2POBoolType(C2POType):
    """Boolean C2PO type."""

    def __init__(self, const: bool):
        super().__init__(C2POBaseType.BOOL, const, 'bool')


class C2POIntType(C2POType):
    """Integer C2PO type with configurable width and signedness."""
    width: int = 8
    is_signed: bool = False

    def __init__(self, const: bool):
        super().__init__(C2POBaseType.INT, const, 'int')


class C2POFloatType(C2POType):
    """Floating point C2PO type with configurable width."""
    width: int = 32

    def __init__(self, const: bool):
        super().__init__(C2POBaseType.FLOAT, const, 'float')


class C2POStructType(C2POType):
    """Structured date C2PO type represented via a name."""

    def __init__(self, const: bool, n: str):
        super().__init__(C2POBaseType.STRUCT, const, n)
        self.name = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,C2POStructType):
            return self.name == arg.name
        return False 


class C2POSetType(C2POType):
    """Parameterized set C2PO type."""

    def __init__(self, const: bool, m: C2POType):
        super().__init__(C2POBaseType.SET, const, 'set<'+str(m)+'>')
        self.member_type: C2POType = m

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            if isinstance(arg,C2POSetType):
                return self.member_type.__eq__(arg.member_type)
        return False


def is_integer_type(t: C2POType) -> bool:
    return isinstance(t, C2POIntType) or isinstance(t, C2POBoolType)


def is_float_type(t: C2POType) -> bool:
    return isinstance(t, C2POFloatType)


def set_types(impl: R2U2Implementation, int_width: int, int_signed: bool, float_width: int):
    """Check for valid int and float widths and configure program types accordingly."""
    C2POIntType.is_signed = int_signed

    if int_width < 1:
        logger.error(f" Invalid int width, must be greater than 0")

    if float_width < 1:
        logger.error(f" Invalid float_width width, must be greater than 0")

    if int_width % 8 != 0:
        logger.error(f" Invalid int width, must be a multiple of 8 for byte-alignment.")

    if float_width % 8 != 0:
        logger.error(f" Invalid float width, must be a multiple of 8 for byte-alignment.")

    if impl == R2U2Implementation.C or impl == R2U2Implementation.CPP:
        if int_width == 8 or int_width == 16 or int_width == 32 or int_width == 64:
            C2POIntType.width = int_width
        else:
            logger.error(f" Invalid int width, must correspond to a C standard int width (8, 16, 32, or 64).")

        if float_width == 32 or float_width == 64:
            C2POFloatType.width = float_width
        else:
            logger.error(f" Invalid float width, must correspond to a C standard float width (32 or 64).")
    else:
        C2POIntType.width = int_width
        C2POFloatType.width = float_width
