import enum
from typing import Optional

MODULE_CODE = "TYPE"

class R2U2Engine(enum.Enum):
    NONE = "NONE"
    SYSTEM = "SYS"
    CONFIG = "CFG"
    # Original Atomic Checker was 3, but has been removed since v4.0
    TEMPORAL_LOGIC = "TL"
    BOOLEANIZER = "BZ"

SignalMapping = dict[str, int]

class BaseType(enum.Enum):
    NOTYPE = "notype"
    BOOL = "bool"
    INT = "int"
    FLOAT = "float"
    ARRAY = "array"
    STRUCT = "struct"
    CONTRACT = "contract"
    ENUM = "enum"

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
    width: int = 32
    is_signed: bool = True

    def __init__(self, is_const: bool = False):
        super().__init__(BaseType.INT, is_const, "int")

class FloatType(Type):
    """Floating point C2PO type with configurable width."""
    width: int = 64

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
    
class EnumType(Type):
    """Structured date C2PO type represented via a name."""

    def __init__(self, symbol: str):
        super().__init__(BaseType.ENUM, True, symbol)

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg, EnumType):
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
            if self.member_type != arg.member_type:
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
    return isinstance(t, IntType) or isinstance(t, BoolType) or isinstance(t, EnumType)

def is_float_type(t: Type) -> bool:
    return isinstance(t, FloatType)

def is_struct_type(t: Type, symbol: Optional[str] = None) -> bool:
    """Returns true if `t` is a `StructType` and, if provided, has symbol `symbol`."""
    if symbol:
        return isinstance(t, StructType) and t.symbol == symbol
    return isinstance(t, StructType)

def is_enum_type(t: Type) -> bool:
    return isinstance(t, EnumType)

def is_array_type(t: Type) -> bool:
    return isinstance(t, ArrayType)
