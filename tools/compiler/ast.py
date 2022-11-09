from __future__ import annotations
from enum import Enum
from typing import NamedTuple, cast
from logging import getLogger

from .util import *
from .types import *

logger = getLogger(logger_name)

class Interval(NamedTuple):
    lb: int
    ub: int

class AST():

    def __init__(self, ln: int, c: list['AST']) -> None:
        self.ln: int = ln
        self.tlid: int = -1
        self.bzid: int = -1
        self.scq_size: int = 0
        self.name: str = ''
        self.bpd: int = 0
        self.wpd: int = 0
        self.formula_type = FormulaType.PROP
        self.type: Type = NoType()
        self.children: list[AST] = []
        self.is_ft: bool = True

        self.parents: list[AST] = []

        child: AST
        for child in c:
            self.children.append(child)

    def __str__(self) -> str:
        return self.name


class EXPR(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)


class TL_EXPR(EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def tlasm(self) -> str:
        return 'n' + str(self.tlid) + ': '


class BZ_EXPR(EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def bzasm(self) -> str:
        return ''


class LIT(BZ_EXPR):

    def __init__(self, ln: int) -> None:
        super().__init__(ln,[])


class CONST(LIT):

    def __init__(self, ln: int) -> None:
        super().__init__(ln)


class INT(CONST):
    
    def __init__(self, ln: int, v: int) -> None:
        super().__init__(ln)
        self.type = Int()
        self.val: int = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name

    def bzasm(self) -> str:
        return 'iconst ' + str(self.name) + '\n'


class FLOAT(CONST):
    
    def __init__(self, ln: int, v: float) -> None:
        super().__init__(ln)
        self.type = Float()
        self.val: float = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name

    def bzasm(self) -> str:
        return 'fconst ' + str(self.name) + '\n'


class SIGNAL(LIT):
    
    def __init__(self, ln: int, n: str, t: Type) -> None:
        super().__init__(ln,)
        self.name: str = n
        self.type: Type = t
        self.sid = -1

    def __str__(self) -> str:
        return self.name

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'load s' + str(self.sid) + '\n'


class BOOL(CONST):
    
    def __init__(self, ln: int, v: bool) -> None:
        super().__init__(ln)
        self.type = Bool()
        self.bpd: int = 0
        self.wpd: int = 0
        self.val: bool = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name


class SET(BZ_EXPR):
    
    def __init__(self, ln: int, m: list[AST]) -> None:
        super().__init__(ln,m)

    def __str__(self) -> str:
        s: str = '{'
        for m in self.children:
            s += str(m) + ','
        s = s[:-1] + '}'
        return s

    def bzasm(self) -> str:
        return 'set ' + str(self.name) + '\n'


class STRUCT(EXPR):

    def __init__(self, ln: int, n: str, m: dict[str,EXPR]) -> None:
        super().__init__(ln,[mem for mem in m.values()])
        self.type: Type = Struct(n)
        self.name: str = n
        self.members: dict[str,EXPR] = m

    def __str__(self) -> str:
        s: str = ''
        s += self.name + '('
        for i,e in self.members.items():
            s += i + '=' + str(e) + ','  
        s = s[:-1] + ')'
        return s


class FUNCTION(EXPR):

    def __init__(self, ln: int, n: str, r: Type, a: list[AST]) -> None:
        super().__init__(ln, a)
        self.name: str = n
        self.type: Type = r



class ATOM(TL_EXPR,BZ_EXPR):
    
    def __init__(self, ln: int, c: AST, a: int) -> None:
        super().__init__(ln,[c])
        self.type: Type = Bool()
        self.bpd: int = 0
        self.wpd: int = 0
        self.atid: int = a

    def __str__(self) -> str:
        return f'{self.children[0]!s}'

    def tlasm(self) -> str:
        return super().tlasm() + 'load a' + str(self.atid) + '\n'

    def bzasm(self) -> str:
        return 'store a' + str(self.atid) + '\n'


class LOG_OP(TL_EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)


class LOG_BIN_OP(LOG_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])
        self.bpd = min(lhs.bpd, rhs.bpd)
        self.wpd = max(lhs.wpd, rhs.wpd)

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


class LOG_UNARY_OP(LOG_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln,[o])
        self.bpd = o.bpd
        self.wpd = o.wpd

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class TL_OP(TL_EXPR):

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

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln,[lhs,rhs],l,u)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


class TL_FT_UNARY_OP(TL_FT_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


class TL_PT_BIN_OP(TL_PT_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, [lhs, rhs], l, u)

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


class TL_PT_UNARY_OP(TL_PT_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


class BW_OP(BZ_EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)


class BW_BIN_OP(BW_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


class BW_UNARY_OP(BW_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln,[o])

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class ARITH_OP(BZ_EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


class ARITH_BIN_OP(ARITH_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


class ARITH_UNARY_OP(ARITH_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln,[o])

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]})'


class ARITH_ADD_OP(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)


class ARITH_MUL_OP(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)


class REL_OP(BZ_EXPR):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


class LOG_OR(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '||'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'or n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + '\n'


class LOG_AND(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '&&'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'and n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + '\n'


class LOG_XOR(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '^^'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'xor n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + '\n'


class LOG_IMPL(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '->'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'impl n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + '\n'


class TL_UNTIL(TL_FT_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'U'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'until n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_RELEASE(TL_FT_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'R'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'release n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_SINCE(TL_PT_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'S'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'since n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class LOG_NEG(LOG_UNARY_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln, o)
        self.name: str = '!'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        operand: AST = self.children[0]
        return super().tlasm() + 'not n' + str(operand.tlid) + '\n'


class TL_GLOBAL(TL_FT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'G'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        operand: AST = self.children[0]
        return super().tlasm() + 'global n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_FUTURE(TL_FT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'F'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        operand: AST = self.children[0]
        return super().tlasm() + 'future n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_HISTORICAL(TL_PT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'H'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        operand: AST = self.children[0]
        return super().tlasm() + 'his n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_ONCE(TL_PT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'O'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        operand: AST = self.children[0]
        return super().tlasm() + 'once n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class BW_AND(BW_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '&'

    def bzasm(self) -> str:
        return 'and\n'


class BW_OR(BW_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '|'

    def bzasm(self) -> str:
        return 'or\n'


class BW_XOR(BW_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def bzasm(self) -> str:
        return 'xor\n'


class BW_NEG(BW_UNARY_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, o)
        self.name: str = '~'

    def bzasm(self) -> str:
        return 'bwneg\n'


class ARITH_ADD(ARITH_ADD_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'add\n'


class ARITH_SUB(ARITH_ADD_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '-'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'sub\n'


class ARITH_MUL(ARITH_MUL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'mul\n'


class ARITH_DIV(ARITH_MUL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '/'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'div\n'


class ARITH_MOD(ARITH_MUL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '%'

    def bzasm(self) -> str:
        return 'mod\n'


class ARITH_NEG(ARITH_UNARY_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, o)
        self.name: str = '-'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'neg\n'


class REL_EQ(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '=='

    def __str__(self) -> str:
        return super().__str__()

    def bzasm(self) -> str:
        return ('i' if self.children[0].type == Int() else 'f') + 'eq\n'


class REL_NEQ(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '!='

    def __str__(self) -> str:
        return super().__str__()

    def bzasm(self) -> str:
        return ('i' if self.children[0].type == Int() else 'f') + 'neq\n'


class REL_GT(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>'

    def __str__(self) -> str:
        return super().__str__()

    def bzasm(self) -> str:
        return ('i' if self.children[0].type == Int() else 'f') + 'gt\n'


class REL_LT(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<'

    def __str__(self) -> str:
        return super().__str__()

    def bzasm(self) -> str:
        return ('i' if self.children[0].type == Int() else 'f') + 'lt\n'


class REL_GTE(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>='

    def __str__(self) -> str:
        return super().__str__()

    def bzasm(self) -> str:
        return ('i' if self.children[0].type == Int() else 'f') + 'gte\n'


class REL_LTE(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<='

    def __str__(self) -> str:
        return super().__str__()

    def bzasm(self) -> str:
        return ('i' if self.children[0].type == Int() else 'f') + 'lte\n'


class SPEC(TL_EXPR):
    
    def __init__(self, ln: int, lbl: str, f: int, e: EXPR) -> None:
        super().__init__(ln, [e])
        self.name: str = lbl
        self.fnum: int = f

    def __str__(self) -> str:
        return (self.name + ': ' if self.name != '' else '')  + str(self.children[0])

    def tlasm(self) -> str:
        top: AST = self.children[0]
        return super().tlasm() + 'end n' + str(top.tlid) + ' f' + str(self.fnum) + '\n'


class PROGRAM(TL_EXPR):

    def __init__(self, ln: int, s: dict[int,SPEC], c: dict[int,SPEC], o: dict[str,int]) -> None:
        super().__init__(ln, list(s.values()))
        self.specs = s
        self.contracts = c
        self.order = o

    def __str__(self) -> str:
        ret: str = ''
        s: AST
        for s in self.children:
            ret += str(s) + '\n'
        return ret

    def tlasm(self) -> str:
        return super().tlasm() + 'endsequence'

