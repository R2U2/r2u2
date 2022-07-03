from __future__ import annotations
from collections.abc import Callable
from enum import Enum
from typing import Any, NamedTuple, cast
from logging import getLogger

from .util import *

logger = getLogger(logger_name)

class Type(Enum):
    NONE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3


class FormulaType(Enum):
    PROP = 0
    FT = 1
    PT = 2


def to_str(t: Type) -> str:
    if t == Type.BOOL:
        return 'bool'
    elif t == Type.INT:
        return 'int'
    elif t == Type.FLOAT:
        return 'float'
    else:
        return ''


class Interval(NamedTuple):
    lb: int
    ub: int


class AST():

    def __init__(self, ln: int, c: list[AST]) -> None:
        self.ln: int = ln
        self.nid: int = -1
        self.id: str = str(self.nid)
        self.scq_size: int = -1
        self.name: str = ''
        self.bpd: int = 0
        self.wpd: int = 0
        self.formula_type = FormulaType.PROP
        self._type: Type = Type.NONE
        self.children: list[AST] = []

        child: AST
        for child in c:
            self.children.append(child)

    def asm(self) -> str:
        return "n"+str(self.nid)+": "


class EXPR(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)


class LIT(EXPR):  

    def __init__(self, ln: int) -> None:
        super().__init__(ln,[])


class CONST(LIT):

    def __init__(self, ln: int) -> None:
        super().__init__(ln)
        self.bpd: int = 0
        self.wpd: int = 0


class BOOL(CONST):
    
    def __init__(self, ln: int, v: bool) -> None:
        super().__init__(ln)
        self._type = Type.BOOL
        self.val: bool = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name


class INT(CONST):
    
    def __init__(self, ln: int, v: int) -> None:
        super().__init__(ln)
        self._type = Type.INT
        self.val: int = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name


class FLOAT(CONST):
    
    def __init__(self, ln: int, v: float) -> None:
        super().__init__(ln)
        self._type = Type.FLOAT
        self.val: float = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name


class VAR(LIT):
    
    def __init__(self, ln: int, n: str, t: Type) -> None:
        super().__init__(ln,)
        self.name: str = n
        self._type: Type = t
        self.sid = -1

    def __str__(self) -> str:
        return self.name

    def asm(self, a: int) -> str:
        return 'a' + str(a) + ': ' + to_str(self._type) + ' == ' + '1 s' + str(self.sid) + '\n'


class ATOM(LIT):
    
    def __init__(self, ln: int, n: str, a: int) -> None:
        super().__init__(ln,)
        self._type: Type = Type.BOOL
        self.bpd: int = 0
        self.wpd: int = 0
        self.name: str = n
        self.aid: int = a

    def __str__(self) -> str:
        return self.name

    def asm(self) -> str:
        return super().asm() + 'load ' + self.name + '\n'


class LOG_OP(EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)


class LOG_BIN_OP(LOG_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln,[lhs, rhs])
        self.bpd = min(lhs.bpd, rhs.bpd)
        self.wpd = max(lhs.wpd, rhs.wpd)

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


class LOG_UNARY_OP(LOG_OP):

    def __init__(self, ln: int, o: EXPR):
        super().__init__(ln,[o])
        self.bpd = o.bpd
        self.wpd = o.wpd

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class REL_OP(EXPR):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln,[lhs, rhs])

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'

    def asm(self, a: int) -> str:
        a1: str
        a2: str

        if isinstance(self.children[0],CONST):
            a1 = self.children[0].name
        else:
            tmp = cast(VAR,self.children[0])
            a1 = 's'+str(tmp.sid)

        if isinstance(self.children[1],CONST):
            a2 = self.children[1].name
        else:
            tmp = cast(VAR,self.children[1])
            a2 = 's'+str(tmp.sid)

        return 'a' + str(a) + ': ' + to_str(self.children[0]._type) + ' ' + self.name + ' ' + a2 + ' ' + a1 + '\n'


class TL_OP(EXPR):

    def __init__(self, ln: int, c: list[AST], l: int, u: int) -> None:
        super().__init__(ln,c)
        self.interval = Interval(lb=l,ub=u)


class TL_FT_OP(TL_OP):

    def __init__(self, ln: int, c: list[AST], l: int, u: int) -> None:
        super().__init__(ln,c,l,u)


class TL_PT_OP(TL_OP):

    def __init__(self, ln: int, c: list[AST], l: int, u: int) -> None:
        super().__init__(ln,c,l,u)


class TL_FT_BIN_OP(TL_FT_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(ln,[lhs,rhs],l,u)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


class TL_FT_UNARY_OP(TL_FT_OP):

    def __init__(self, ln: int, o: EXPR, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


class TL_PT_BIN_OP(TL_PT_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(ln, [lhs, rhs], l, u)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


class TL_PT_UNARY_OP(TL_PT_OP):

    def __init__(self, ln: int, o: EXPR, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


class TERNARY_OP(EXPR):

    def __init__(self, ln: int, arg1: EXPR , arg2: EXPR, arg3: EXPR) -> None:
        super().__init__(ln, [arg1,arg2,arg3])
        self.name: str = 'ite'

    def __str__(self) -> str:
        arg1: AST = self.children[0]
        arg2: AST = self.children[1]
        arg3: AST = self.children[2]
        return '(' + str(arg1) + ')?(' + str(arg2) + '):(' + str(arg3) + ')'


class LOG_OR(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '||'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'or ' + lhs.id + ' ' + rhs.id + '\n'


class LOG_AND(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '||'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'and ' + lhs.id + ' ' + rhs.id + '\n'


class REL_EQ(REL_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '=='

    def __str__(self) -> str:
        return super().__str__()


class REL_NEQ(REL_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '!='

    def __str__(self) -> str:
        return super().__str__()


class REL_GT(REL_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>'

    def __str__(self) -> str:
        return super().__str__()


class REL_LT(REL_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<'

    def __str__(self) -> str:
        return super().__str__()


class REL_GTE(REL_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>='

    def __str__(self) -> str:
        return super().__str__()


class REL_LTE(REL_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<='

    def __str__(self) -> str:
        return super().__str__()


class TL_UNTIL(TL_FT_BIN_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'U'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'until ' + lhs.id + ' ' + rhs.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_RELEASE(TL_FT_BIN_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'R'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'release ' + lhs.id + ' ' + rhs.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_SINCE(TL_PT_BIN_OP):

    def __init__(self, ln: int, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'S'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'since ' + lhs.id + ' ' + rhs.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class LOG_NEG(LOG_UNARY_OP):

    def __init__(self, ln: int, o: EXPR):
        super().__init__(ln, o)
        self.name: str = '!'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'not ' + operand.id


class TL_GLOBAL(TL_FT_UNARY_OP):

    def __init__(self, ln: int, o: EXPR, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'G'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'global ' + operand.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_FUTURE(TL_FT_UNARY_OP):

    def __init__(self, ln: int, o: EXPR, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'F'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'future ' + operand.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_HISTORICAL(TL_PT_UNARY_OP):

    def __init__(self, ln: int, o: EXPR, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'H'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'his n' + operand.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_ONCE(TL_PT_UNARY_OP):
    pass


class SPEC(AST):
    
    def __init__(self, ln: int, lbl: str, f: int, e: EXPR) -> None:
        super().__init__(ln, [e])
        self.name: str = lbl
        self.fnum = f

    def __str__(self) -> str:
        return self.name + ': ' + str(self.children[0])

    def asm(self) -> str:
        top: AST = self.children[0]
        return super().asm() + 'end ' + top.id + ' ' + str(self.fnum) + '\n'


class PROGRAM(AST):

    def __init__(self, ln: int, s: dict[int,SPEC], o: dict[str,int]) -> None:
        super().__init__(ln, list(s.values()))
        self.order = o

    def __str__(self) -> str:
        ret: str = ''
        s: AST
        for s in self.children:
            ret += str(s) + '\n'
        return ret

    def asm(self) -> str:
        return super().asm() + 'end sequence'

