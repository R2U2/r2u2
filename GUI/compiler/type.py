from enum import Enum

# class BaseType(Enum):
#     NOTYPE = 0
#     BOOL = 1
#     INT8 = 2
#     INT16 = 3
#     INT32 = 4
#     INT64 = 5
#     UINT8 = 6
#     UINT16 = 7
#     UINT32 = 8
#     UINT64 = 9
#     FLOAT = 10
#     DOUBLE = 11
#     SET = 12
#     STRUCT = 13

class BaseType(Enum):
    NOTYPE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3
    SET = 4
    STRUCT = 5


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


class NOTYPE(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.NOTYPE,'none')


class BOOL(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.BOOL,'bool')


class INT(Type):
    ctype: str = 'uint8_t'

    def __init__(self) -> None:
        super().__init__(BaseType.INT,'int')


class FLOAT(Type):
    ctype: str = 'float'

    def __init__(self) -> None:
        super().__init__(BaseType.FLOAT,'float')


class STRUCT(Type):

    def __init__(self, n: str) -> None:
        super().__init__(BaseType.STRUCT,n)
        self.name = n

    def __eq__(self, arg: object) -> bool:
        if isinstance(arg,STRUCT):
            return self.name == arg.name
        return False 


class SET(Type):

    def __init__(self, m: Type) -> None:
        super().__init__(BaseType.SET,'set<'+str(m)+'>')
        self.member_type: Type = m

    def __eq__(self, arg: object) -> bool:
        if super().__eq__(arg):
            if isinstance(arg,SET):
                return self.member_type.__eq__(arg.member_type)
        return False


def is_integer_type(t: Type) -> bool:
    return isinstance(t,INT) or isinstance(t,BOOL)


def is_float_type(t: Type) -> bool:
    return isinstance(t,FLOAT)


class FormulaType(Enum):
    PROP = 0
    FT = 1
    PT = 2

