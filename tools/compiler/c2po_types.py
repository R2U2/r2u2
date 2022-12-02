from enum import Enum

class BaseType(Enum):
    NOTYPE = 0
    BOOL = 1
    UINT8 = 2
    UINT16 = 3
    UINT32 = 4
    UINT64 = 5
    SINT8 = 6
    SINT16 = 7
    SINT32 = 8
    SINT64 = 9
    FLOAT = 10
    DOUBLE = 11
    SET = 12
    STRUCT = 13

class Type():

    def __init__(self, t: BaseType, n: str) -> None:
        self.value: BaseType = t
        self.name: str = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,Type):
            return self.value == arg.value
        return False

    def __str__(self) -> str:
        return self.name

class NoType(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.NOTYPE,'none')

class Bool(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.BOOL,'bool')

class Int(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.UINT8,'int')

class Float(Type):
    def __init__(self) -> None:
        super().__init__(BaseType.FLOAT,'float')

class Struct(Type):
    def __init__(self, n: str) -> None:
        super().__init__(BaseType.STRUCT,n)
        self.name = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,Struct):
            return self.name == arg.name
        return False 

class Set(Type):
    def __init__(self, m: Type) -> None:
        super().__init__(BaseType.SET,'set<'+str(m)+'>')
        self.member_type: Type = m

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            if isinstance(arg,Set):
                return self.member_type.__eq__(arg.member_type)
        return False

class FormulaType(Enum):
    PROP = 0
    FT = 1
    PT = 2
