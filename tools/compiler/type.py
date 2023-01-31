from enum import Enum

class BaseType(Enum):
    NOTYPE = 0
    BOOL = 1
    INT8 = 2
    INT16 = 3
    INT32 = 4
    INT64 = 5
    UINT8 = 6
    UINT16 = 7
    UINT32 = 8
    UINT64 = 9
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


class NOTYPE(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.NOTYPE,'none')


class BOOL(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.BOOL,'bool')


class INT8(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.INT8,'int8')


class INT16(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.INT16,'int16')


class INT32(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.INT32,'int32')


class INT64(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.INT64,'int64')


class UINT8(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.UINT8,'uint8')


class UINT16(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.UINT16,'uint16')


class UINT32(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.UINT32,'uint32')


class UINT64(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.UINT64,'uint64')


class FLOAT(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.FLOAT,'float')


class DOUBLE(Type):

    def __init__(self) -> None:
        super().__init__(BaseType.DOUBLE,'double')


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
    return isinstance(t,INT8) or isinstance(t,INT16) or isinstance(t,INT32) or isinstance(t,INT64) or \
        isinstance(t,UINT8) or isinstance(t,UINT16) or isinstance(t,UINT32) or isinstance(t,UINT64) or \
            isinstance(t,BOOL)


def is_float_type(t: Type) -> bool:
    return isinstance(t,FLOAT) or isinstance(t,DOUBLE)


class FormulaType(Enum):
    PROP = 0
    FT = 1
    PT = 2
