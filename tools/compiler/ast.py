from dataclasses import dataclass
from enum import Enum

class Type(Enum):
    _NONE = 0
    _BOOL = 1
    _INT = 2
    _FLOAT = 3


# class Op(Enum):
#     __NONE = -1
#     __LOG_NEG = 0
#     __LOG_AND = 1
#     __LOG_OR = 2
#     __LOG_XOR = 3
#     __LOG_IMPL = 4
#     __LOG_IFF = 5
#     __BW_NEG = 10
#     __BW_AND = 11
#     __BW_OR = 12
#     __BW_XOR = 13
#     __REL_EQ = 20
#     __REL_NEQ = 21
#     __REL_GT = 22
#     __REL_LT = 23
#     __REL_GTE = 24
#     __REL_LTE = 25
#     __ARITH_ADD = 30
#     __ARITH_SUB = 31
#     __ARITH_MUL = 32
#     __ARITH_DIV = 33
#     __ARITH_MOD = 34
#     __ARITH_POW = 35
#     __ARITH_SQRT = 36
#     __ARITH_PM = 37
#     __ARITH_NEG = 38
#     __TL_GLOBAL = 40
#     __TL_FUTURE = 41
#     __TL_NEXT = 42
#     __TL_SINCE = 43
#     __TL_ONCE = 44
#     __TL_UNTIL = 45
#     __TL_RELEASE = 46
#     __TL_HISTORICAL = 47
#     __FO_FORALL = 50
#     __FO_EXISTS = 51
#     __SW_MEMBER = 60
#     __SW_SUBSET = 61
#     __SW_SUBSETEQ = 62
#     __SW_SUPSET = 63
#     __SW_SUPSETEQ = 64
#     __SW_SUM = 65
#     __SW_PROD = 66
#     __SW_UNION = 67
#     __SW_INTERSECTION = 68
#     __SW_AND = 69
#     __SW_OR = 70
#     __SW_CTPROD = 71



@dataclass
class AST():
    lineno: int


@dataclass
class EXPR(AST):
    _type: Type


@dataclass
class CONST(EXPR):
    pass


@dataclass
class BOOL(CONST):
    val: bool
    _type = Type._BOOL


@dataclass
class INT(CONST):
    val: int
    _type = Type._INT


@dataclass
class FLOAT(CONST):
    val: float
    _type = Type._FLOAT


@dataclass
class VAR(EXPR):
    name: str


class ATOM(EXPR):
    name: str

    def gen_assembly(self, s):
        # substr = "load "+self.name
        # s = super().gen_assembly(s, substr)
        return s


@dataclass
class BIN_OP(EXPR):
    left: EXPR
    right: EXPR
    pass


@dataclass
class LOG_OR(BIN_OP):
    pass


@dataclass
class LOG_AND(BIN_OP):
    pass


@dataclass
class REL_EQ(BIN_OP):
    pass


@dataclass
class REL_NEQ(BIN_OP):
    pass


@dataclass
class REL_GT(BIN_OP):
    pass


@dataclass
class REL_LT(BIN_OP):
    pass


@dataclass
class REL_GTE(BIN_OP):
    pass


@dataclass
class REL_LTE(BIN_OP):
    pass


@dataclass
class TL_UNTIL(BIN_OP):
    interval: tuple[int,int]


@dataclass
class TL_RELEASE(BIN_OP):
    interval: tuple[int,int]


@dataclass
class TL_SINCE(BIN_OP):
    interval: tuple[int,int]


@dataclass
class UNARY_OP(EXPR):
    operand: EXPR


@dataclass
class LOG_NEG(UNARY_OP):
    pass


@dataclass
class ARITH_NEG(UNARY_OP):
    pass


@dataclass
class TL_GLOBAL(UNARY_OP):
    interval: tuple[int,int]


@dataclass
class TL_FUTURE(UNARY_OP):
    interval: tuple[int,int]


@dataclass
class TL_HISTORICAL(UNARY_OP):
    interval: tuple[int,int]


@dataclass
class TL_ONCE(UNARY_OP):
    interval: tuple[int,int]


@dataclass
class SPEC(AST):
    child: EXPR
    label: str = ""

    def gen_assembly(self, s):
        # substr = 'end '+self.child.hook
        # self.hook = 's'+str(Observer.line_cnt)
        # s += self.hook+": "+substr+ ' '+str(self.formula_num)+ '\n'
        # Observer.line_cnt += 1
        return s


@dataclass
class PROGRAM(AST):
    vars: dict[str,Type]
    specs: dict[tuple[int,str],SPEC] # (spec_num, label) -> spec