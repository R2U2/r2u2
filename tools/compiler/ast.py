from __future__ import annotations
from copy import deepcopy
from typing import Any, Callable, NamedTuple, NewType, cast
from logging import getLogger

from .util import *
from .c2po_types import *

logger = getLogger(logger_name)


class Interval(NamedTuple):
    lb: int
    ub: int


StructDict = NewType('StructDict',dict[str,dict[str,Type]])


def postorder(a: AST, func: Callable[[AST],Any]) -> None:
    c: AST
    for c in a.children:
        postorder(c,func)
    func(a)


def preorder(a: AST, func: Callable[[AST],Any]) -> None:
    c: AST
    func(a)
    for c in a.children:
        preorder(c,func)


def traverse(a: AST, pre: Callable[[AST],Any], post: Callable[[AST],Any]) -> None:
    c: AST
    pre(a)
    for c in a.children:
        traverse(c,pre,post)
    post(a)


# precondition: all children are properly set
def set_parents(prog: AST) -> None:

    def set_parents_util(a: AST) -> None:
        for c in a.children:
            c.parents.append(a)

    postorder(prog,set_parents_util)


def set_type(s: AST, expr: AST, t: Type) -> None:

    def set_type_util(a: AST) -> None:
        if s == a:
            a.type = t

    postorder(expr,set_type_util)


# replace AST old with AST new by pointing all of old's parents to new
# and setting new's parents accordingly
def rewrite(old: AST, new: AST) -> None:
    for p in old.parents:
        for i in range(0,len(p.children)):
            if p.children[i] == old:
                p.children[i] = new
        new.parents.append(p)


def rename(v: AST, repl: AST, expr: AST) -> AST:
    new: AST = deepcopy(expr)

    def rename_util(a: AST) -> None:
        if v == a:
            rewrite(a,repl)

    postorder(new,rename_util)
    return new


class AST():

    def __init__(self, ln: int, c: list['AST']) -> None:
        self.ln: int = ln
        self.tlid: int = -1
        self.bzid: int = -1
        self.atid: int = -1
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


class TL_EXPR(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def tlasm(self) -> str:
        return 'n' + str(self.tlid) + ': '


class BZ_EXPR(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def tlasm(self) -> str:
        return f'n{str(self.tlid)}: load a{str(self.atid)}\n' 

    def bzasm(self) -> str:
        return ''

    def bzasm_store(self) -> str:
        return f'store a{self.atid}\n'

    def bzasm_dup(self) -> str:
        return 'dup\n'


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


class VAR(AST):

    def __init__(self, ln: int, n: str) -> None:
        super().__init__(ln,[])
        self.name: str = n
        self.reg: int = -1

    def __str__(self) -> str:
        return self.name

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o,VAR) and __o.name == self.name

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + f'load r{self.reg}'


class SIGNAL(LIT):
    
    def __init__(self, ln: int, n: str, t: Type) -> None:
        super().__init__(ln,)
        self.name: str = n
        self.type: Type = t
        self.sid = -1

    def __str__(self) -> str:
        return self.name

    def tlasm(self) -> str:
        return super().tlasm() + f'load s{self.sid}\n'

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
    
    def __init__(self, ln: int, max: int, m: list[AST]) -> None:
        super().__init__(ln,m)
        self.max_size: int = max
        self.dynamic_size = None

    def get_max_size(self) -> int:
        return self.max_size

    def get_dynamic_size(self) -> AST|None:
        return self.dynamic_size

    def set_dynamic_size(self, s: AST) -> None:
        self.dynamic_size = s

    def __str__(self) -> str:
        s: str = '{'
        for m in self.children:
            s += str(m) + ','
        s = s[:-1] + '}'
        return s

    def bzasm(self) -> str:
        return 'set ' + str(self.name) + '\n'


class STRUCT(AST):

    def __init__(self, ln: int, n: str, m: dict[str,AST]) -> None:
        super().__init__(ln,[mem for mem in m.values()])
        self.type: Type = Struct(n)
        self.name: str = n
        self.members: dict[str,AST] = m

    def __str__(self) -> str:
        s: str = ''
        s += self.name + '('
        for i,e in self.members.items():
            s += i + '=' + str(e) + ','  
        s = s[:-1] + ')'
        return s


class STRUCT_ACCESS(AST):

    def __init__(self, ln: int, s: AST, m: str) -> None:
        super().__init__(ln, [s])
        self.member: str = m

    def get_struct(self) -> AST:
        return self.children[0]

    def __str__(self) -> str:
        return str(self.children[0]) + '.' + self.member


class FUNCTION(AST):

    def __init__(self, ln: int, n: str, r: Type, a: list[AST]) -> None:
        super().__init__(ln, a)
        self.name: str = n
        self.type: Type = r


class SET_AGG_OP(AST):

    def __init__(self, ln: int, s: SET, v: VAR,  e: AST) -> None:
        super().__init__(ln,[s,v,e])

    def get_set(self) -> SET:
        return cast(SET,self.children[0])

    def get_boundvar(self) -> VAR:
        return cast(VAR,self.children[1])

    def get_expr(self) -> AST:
        return self.children[2]

    def __str__(self) -> str:
        return self.name + '(' + str(self.get_boundvar()) + ':' + str(self.get_set()) + ')' + '(' + str(self.get_expr()) + ')'


class FOR_EACH(SET_AGG_OP):

    def __init__(self, ln: int, s: SET, v: VAR, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'foreach'


class FOR_SOME(SET_AGG_OP):

    def __init__(self, ln: int, s: SET, v: VAR, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'forsome'


class FOR_EXACTLY_N(SET_AGG_OP):

    def __init__(self, ln: int, s: SET, n: int, v: VAR, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'forexactlyn'
        self.num: int = n


class FOR_AT_LEAST_N(SET_AGG_OP):

    def __init__(self, ln: int, s: SET, n: int, v: VAR, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'foratleastn'
        self.num: int = n


class FOR_AT_MOST_N(SET_AGG_OP):

    def __init__(self, ln: int, s: SET, n: int, v: VAR, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'foratmostn'
        self.num: int = n


class COUNT(BZ_EXPR):

    def __init__(self, ln: int, n: AST, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.num: AST = n

    def tlasm(self) -> str:
        s: str = ''
        # s += 
        s += f'popn\n'
        s += f'count {self.num}\n'
        return s


class BW_OP(BZ_EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)


class BW_BIN_OP(BW_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


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


class BW_UNARY_OP(BW_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln,[o])

    def get_operand(self) -> AST:
        return self.children[0]

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class BW_NEG(BW_UNARY_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, o)
        self.name: str = '~'

    def bzasm(self) -> str:
        return 'bwneg\n'


class ARITH_OP(BZ_EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


class ARITH_BIN_OP(ARITH_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


class ARITH_ADD(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'add\n'


class ARITH_SUB(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '-'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'sub\n'


class ARITH_MUL(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'mul\n'


class ARITH_DIV(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '/'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'div\n'


class ARITH_MOD(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '%'

    def bzasm(self) -> str:
        return 'mod\n'


class ARITH_UNARY_OP(ARITH_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln,[o])

    def get_operand(self) -> AST:
        return self.children[0]

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]})'


class ARITH_NEG(ARITH_UNARY_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, o)
        self.name: str = '-'

    def bzasm(self) -> str:
        return ('f' if self.type == Float() else 'i') + 'neg\n'


class REL_OP(BZ_EXPR):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs,rhs])

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


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

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


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


class TL_FT_UNARY_OP(TL_FT_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def get_operand(self) -> AST:
        return self.children[0]

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


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


class TL_PT_BIN_OP(TL_PT_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, [lhs, rhs], l, u)

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


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


class TL_PT_UNARY_OP(TL_PT_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)

    def get_operand(self) -> AST:
        return self.children[0]

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


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


class LOG_OP(TL_EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)


class LOG_OR(LOG_OP):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.name: str = '||'

    def __str__(self) -> str:
        s: str = ''
        for arg in self.children:
            s += str(arg) + '||'
        return s[:-2]

    def tlasm(self) -> str:
        s: str = super().tlasm() + 'or'
        for c in self.children:
            s += ' n' + str(c.tlid)
        return s + '\n'


class LOG_AND(LOG_OP):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.name: str = '&&'

    def __str__(self) -> str:
        s: str = ''
        for arg in self.children:
            s += str(arg) + '&&'
        return s[:-2]

    def tlasm(self) -> str:
        s: str = super().tlasm() + 'and'
        for c in self.children:
            s += ' n' + str(c.tlid)
        return s + '\n'


class LOG_BIN_OP(LOG_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])
        self.bpd = min(lhs.bpd, rhs.bpd)
        self.wpd = max(lhs.wpd, rhs.wpd)

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


class LOG_BIN_OR(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '||'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().tlasm() + 'or n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + '\n'


class LOG_BIN_AND(LOG_BIN_OP):

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


class LOG_UNARY_OP(LOG_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln,[o])
        self.bpd = o.bpd
        self.wpd = o.wpd

    def get_operand(self) -> AST:
        return self.children[0]

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class LOG_NEG(LOG_UNARY_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln, o)
        self.name: str = '!'

    def __str__(self) -> str:
        return super().__str__()

    def tlasm(self) -> str:
        operand: AST = self.children[0]
        return super().tlasm() + 'not n' + str(operand.tlid) + '\n'


class SPEC(TL_EXPR):
    
    def __init__(self, ln: int, lbl: str, f: int, e: AST) -> None:
        super().__init__(ln, [e])
        self.name: str = lbl
        self.fnum: int = f

    def get_expr(self) -> AST:
        return self.children[0]

    def __str__(self) -> str:
        return (self.name + ': ' if self.name != '' else '')  + str(self.children[0])

    def tlasm(self) -> str:
        top: AST = self.children[0]
        return super().tlasm() + 'end n' + str(top.tlid) + ' f' + str(self.fnum) + '\n'


class PROGRAM(TL_EXPR):

    def __init__(self, ln: int, st: StructDict, s: dict[int,SPEC], c: dict[int,SPEC]) -> None:
        super().__init__(ln, list(s.values()))
        self.structs = st
        self.specs = s
        self.contracts = c

    def __str__(self) -> str:
        ret: str = ''
        s: AST
        for s in self.children:
            ret += str(s) + '\n'
        return ret

    def tlasm(self) -> str:
        return super().tlasm() + 'endsequence'

