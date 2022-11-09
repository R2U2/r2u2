from enum import Enum
from typing import cast

class Type():
    NOTYPE: int = 0
    BOOL: int = 1
    INT: int = 2
    FLOAT: int = 3
    SET: int = 4
    STRUCT: int = 5

    def __init__(self, t: int) -> None:
        self.value: int = t

    def __eq__(self, arg: object) -> bool:
        try:
            assert isinstance(arg,Type)
            return self.value == arg.value
        except AssertionError:
            return False

    def __str__(self) -> str:
        if self.value == Type.BOOL:
            return 'bool'
        elif self.value == Type.INT:
            return 'int'
        elif self.value == Type.FLOAT:
            return 'float'
        return 'none'

class NoType(Type):
    def __init__(self) -> None:
        super().__init__(Type.NOTYPE)

class Bool(Type):
    def __init__(self) -> None:
        super().__init__(Type.BOOL)

class Int(Type):
    def __init__(self) -> None:
        super().__init__(Type.INT)

class Float(Type):
    def __init__(self) -> None:
        super().__init__(Type.FLOAT)

class Struct(Type):
    def __init__(self, n: str) -> None:
        super().__init__(Type.STRUCT)
        self.name = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,Struct):
            return self.name == arg.name
        else:
            return False 

    def __str__(self) -> str:
        return self.name

class Set(Type):
    def __init__(self, m: Type) -> None:
        super().__init__(Type.SET)
        self.member_type: Type = m

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            return self.member_type.__eq__(cast(Set,arg).member_type)
        else:
            return False

    def __str__(self) -> str:
        return 'set<' + str(self.member_type) + '>'


class FormulaType(Enum):
    PROP = 0
    FT = 1
    PT = 2
