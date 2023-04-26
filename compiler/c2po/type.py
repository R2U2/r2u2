from enum import Enum
from logging import getLogger

from .logger import STANDARD_LOGGER_NAME, COLOR_LOGGER_NAME

logger = getLogger(COLOR_LOGGER_NAME)


class R2U2Implementation(Enum):
    C = 0
    CPP = 1
    VHDL = 2


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


class BaseType(Enum):
    NOTYPE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3
    SET = 4
    STRUCT = 5


class Type():
    """Abstract base class representing a C2PO type."""

    def __init__(self, t: BaseType, n: str) -> None:
        self.value: BaseType = t
        self.name: str = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, Type):
            return self.value == arg.value
        return False

    def __str__(self) -> str:
        return self.name


class NOTYPE(Type):
    """An invalid C2PO type."""

    def __init__(self) -> None:
        super().__init__(BaseType.NOTYPE,'none')


class BOOL(Type):
    """Boolean C2PO type."""

    def __init__(self) -> None:
        super().__init__(BaseType.BOOL,'bool')


class INT(Type):
    """Integer C2PO type with configurable width and signedness."""
    width: int = 8
    is_signed: bool = False

    def __init__(self) -> None:
        super().__init__(BaseType.INT, 'int')


class FLOAT(Type):
    """Floating point C2PO type with configurable width."""
    width: int = 32

    def __init__(self) -> None:
        super().__init__(BaseType.FLOAT,'float')


class STRUCT(Type):
    """Structured date C2PO type represented via a name."""

    def __init__(self, n: str) -> None:
        super().__init__(BaseType.STRUCT, n)
        self.name = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,STRUCT):
            return self.name == arg.name
        return False 


class SET(Type):
    """Parameterized set C2PO type."""

    def __init__(self, m: Type) -> None:
        super().__init__(BaseType.SET,'set<'+str(m)+'>')
        self.member_type: Type = m

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            if isinstance(arg,SET):
                return self.member_type.__eq__(arg.member_type)
        return False


def is_integer_type(t: Type) -> bool:
    return isinstance(t, INT) or isinstance(t, BOOL)


def is_float_type(t: Type) -> bool:
    return isinstance(t, FLOAT)


class FormulaType(Enum):
    PROP = 0
    FT = 1
    PT = 2


def set_types(impl: R2U2Implementation, int_width: int, int_signed: bool, float_width: int):
    """Check for valid int and float widths and configure program types accordingly."""
    INT.is_signed = int_signed

    if int_width < 1:
        logger.error(f" Invalid int width, must be greater than 0 (found {int_width})")

    if float_width < 1:
        logger.error(f" Invalid float_width width, must be greater than 0 (found {float_width})")

    if impl == R2U2Implementation.C or impl == R2U2Implementation.CPP:
        if int_width == 8 or int_width == 16 or int_width == 32 or int_width == 64:
            INT.width = int_width
        else:
            logger.error(f" Invalid int width, must correspond to a C standard int width (8, 16, 32, or 64).")

        if float_width == 32 or float_width == 64:
            FLOAT.width = float_width
        else:
            logger.error(f" Invalid float width, must correspond to a C standard float width (32 or 64).")
    else:
        INT.width = int_width
        FLOAT.width = float_width
