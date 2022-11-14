from enum import Enum
from typing import cast

class BaseType(Enum):
    NOTYPE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3
    SET = 4
    STRUCT = 5


class Type():

    def __init__(self, t: BaseType) -> None:
        self.value: BaseType = t

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,Type):
            return self.value == arg.value
        return False

    def __str__(self) -> str:
        if self.value == BaseType.BOOL:
            return 'bool'
        elif self.value == BaseType.INT:
            return 'int'
        elif self.value == BaseType.FLOAT:
            return 'float'
        return 'none'

class NoType(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.NOTYPE)

class Bool(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.BOOL)

class Int(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.INT)

class Float(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.FLOAT)

class Struct(Type):
    def __init__(self, n: str) -> None:
        super().__init__(BaseType.STRUCT)
        self.name = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,Struct):
            return self.name == arg.name
        return False 

    def __str__(self) -> str:
        return self.name

class Set(Type):
    def __init__(self, m: Type) -> None:
        super().__init__(BaseType.SET)
        self.member_type: Type = m

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            if isinstance(arg,Set):
                return self.member_type.__eq__(arg.member_type)
        return False

    def __str__(self) -> str:
        return 'set<' + str(self.member_type) + '>'


class FormulaType(Enum):
    PROP = 0
    FT = 1
    PT = 2
