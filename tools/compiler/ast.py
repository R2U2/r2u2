from __future__ import annotations
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
    new: AST = expr.copy()
    repl.parents = [] # replacement ought to be standalone

    def rename_util(a: AST) -> None:
        if v == a:
            rewrite(a,repl)

    postorder(new,rename_util)
    return new


class AST():

    def __init__(self, ln: int, c: list[AST]) -> None:
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
        self.is_ft: bool = True

        self.children: list[AST] = []
        self.parents: list[AST] = []

        child: AST
        for child in c:
            self.children.append(child)
            child.parents.append(self)

    def __str__(self) -> str:
        return self.name

    def asm(self) -> str:
        return 'ERROR: no asm instruction'

    def copy_attrs(self, new: AST) -> None:
        new.tlid = self.tlid
        new.bzid = self.bzid
        new.atid = self.atid
        new.scq_size = self.scq_size
        new.name = self.name
        new.bpd = self.bpd
        new.wpd = self.wpd
        new.formula_type = self.formula_type
        new.type = self.type
        new.is_ft = self.is_ft

    def copy(self) -> AST:
        children = [c.copy() for c in self.children]
        new = type(self)(self.ln,children)
        self.copy_attrs(new)
        return new


class TL_EXPR(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def asm(self) -> str:
        return 'TL: n' + str(self.tlid) + ': '


class BZ_EXPR(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def asm(self) -> str:
        return 'BZ: '

    def asm_store(self) -> str:
        return f'store a{self.atid}'

    def asm_dup(self) -> str:
        return 'dup'


# only used for assembly generation
class LOAD(TL_EXPR):

    def __init__(self, ln: int, l: AST) -> None:
        super().__init__(ln, [l])
        self.tlid = l.tlid

    def get_load(self) -> AST:
        return self.children[0]
 
    def asm(self) -> str:
        return super().asm() + f'load a{str(self.get_load().atid)}' 


# only used for assembly generation
class DUP(BZ_EXPR):

    def __init__(self, ln: int, d: AST) -> None:
        super().__init__(ln, [d])

    def asm(self) -> str:
        return super().asm() + 'dup'


# only used for assembly generation
class STORE(BZ_EXPR):

    def __init__(self, ln: int, s: AST) -> None:
        super().__init__(ln, [s])

    def get_store(self) -> AST:
        return self.children[0]

    def asm(self) -> str:
        return super().asm() + f'store a{self.get_store().atid}'


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

    def copy(self) -> INT:
        new = INT(self.ln,self.val)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return self.name

    def asm(self) -> str:
        return super().asm() + 'iconst ' + str(self.name) + ''


class FLOAT(CONST):
    
    def __init__(self, ln: int, v: float) -> None:
        super().__init__(ln)
        self.type = Float()
        self.val: float = v
        self.name = str(v)

    def copy(self) -> FLOAT:
        new = FLOAT(self.ln,self.val)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return self.name

    def asm(self) -> str:
        return super().asm() + 'fconst ' + str(self.name) + ''


class VAR(AST):

    def __init__(self, ln: int, n: str) -> None:
        super().__init__(ln,[])
        self.name: str = n
        self.reg: int = -1

    def copy(self) -> VAR:
        new = VAR(self.ln,self.name)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return self.name

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o,VAR) and __o.name == self.name

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == Float() else 'i') + f'load r{self.reg}'


class SIGNAL(LIT):
    
    def __init__(self, ln: int, n: str, t: Type) -> None:
        super().__init__(ln,)
        self.name: str = n
        self.type: Type = t
        self.sid = -1

    def __str__(self) -> str:
        return self.name

    def copy(self) -> SIGNAL:
        new = SIGNAL(self.ln,self.name,self.type)
        new.sid = self.sid
        self.copy_attrs(new)
        return new

    # def asm(self) -> str:
    #     return super().asm() + f'load s{self.sid}'

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == Float() else 'i') + 'load s' + str(self.sid) + ''


class BOOL(CONST):
    
    def __init__(self, ln: int, v: bool) -> None:
        super().__init__(ln)
        self.type = Bool()
        self.bpd: int = 0
        self.wpd: int = 0
        self.val: bool = v
        self.name = str(v)

    def copy(self) -> BOOL:
        new = BOOL(self.ln,self.val)
        self.copy_attrs(new)
        return new

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

    def copy(self) -> SET:
        new = SET(self.ln,self.max_size,[c.copy() for c in self.children])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s: str = '{'
        for m in self.children:
            s += str(m) + ','
        s = s[:-1] + '}'
        return s

    def asm(self) -> str:
        return super().asm() + 'set ' + str(self.name) + ''


class STRUCT(AST):

    def __init__(self, ln: int, n: str, m: dict[str,AST]) -> None:
        super().__init__(ln,[mem for mem in m.values()])
        self.type: Type = Struct(n)
        self.name: str = n
        self.members: dict[str,AST] = m

    def copy(self) -> STRUCT:
        new = STRUCT(self.ln,self.name,self.members)
        self.copy_attrs(new)
        return new

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

    def get_struct(self) -> STRUCT:
        return cast(STRUCT, self.children[0])

    def copy(self) -> STRUCT_ACCESS:
        new = STRUCT_ACCESS(self.ln,self.get_struct().copy(),self.member)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return str(self.children[0]) + '.' + self.member


class FUNCTION(AST):

    def __init__(self, ln: int, n: str, r: Type, a: list[AST]) -> None:
        super().__init__(ln, a)
        self.name: str = n
        self.type: Type = r


class SET_AGG_OP(AST):

    def __init__(self, ln: int, s: AST, v: AST,  e: AST) -> None:
        super().__init__(ln,[s,v,e])

    def get_set(self) -> SET:
        return cast(SET,self.children[0])

    def get_boundvar(self) -> VAR:
        return cast(VAR,self.children[1])

    def get_expr(self) -> AST:
        return self.children[2]

    def copy(self) -> SET_AGG_OP:
        new = type(self)(self.ln,self.get_set().copy(),self.get_boundvar().copy(),self.get_expr().copy())
        self.copy_attrs(new)
        return new

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

    def asm(self) -> str:
        return super().asm() + f'count {self.num}'


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

    def copy(self) -> BW_BIN_OP:
        new = type(self)(self.ln,self.get_lhs().copy(),self.get_rhs().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


class BW_AND(BW_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '&'

    def asm(self) -> str:
        return super().asm() + 'and'


class BW_OR(BW_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '|'

    def asm(self) -> str:
        return super().asm() + 'or'


class BW_XOR(BW_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def asm(self) -> str:
        return super().asm() + 'xor'


class BW_UNARY_OP(BW_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln,[o])

    def get_operand(self) -> AST:
        return self.children[0]

    def copy(self) -> BW_UNARY_OP:
        new = type(self)(self.ln,self.get_operand().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class BW_NEG(BW_UNARY_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, o)
        self.name: str = '~'

    def asm(self) -> str:
        return super().asm() + 'bwneg'


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

    def copy(self) -> ARITH_BIN_OP:
        new = type(self)(self.ln,self.get_lhs().copy(),self.get_rhs().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.children[0]}){self.name!s}({self.children[1]!s})'


class ARITH_ADD(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == Float() else 'i') + 'add'


class ARITH_SUB(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '-'

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == Float() else 'i') + 'sub'


class ARITH_MUL(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '+'

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == Float() else 'i') + 'mul'


class ARITH_DIV(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '/'

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == Float() else 'i') + 'div'


class ARITH_MOD(ARITH_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '%'

    def asm(self) -> str:
        return super().asm() + 'mod'


class ARITH_UNARY_OP(ARITH_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln,[o])

    def get_operand(self) -> AST:
        return self.children[0]

    def copy(self) -> ARITH_UNARY_OP:
        new = type(self)(self.ln,self.get_operand().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]})'


class ARITH_NEG(ARITH_UNARY_OP):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, o)
        self.name: str = '-'

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == Float() else 'i') + 'neg'


class REL_OP(BZ_EXPR):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs,rhs])

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def copy(self) -> REL_OP:
        new = type(self)(self.ln,self.get_lhs().copy(),self.get_rhs().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


class REL_EQ(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '=='

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        return super().asm() + ('i' if self.children[0].type == Int() else 'f') + 'eq'


class REL_NEQ(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '!='

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        return super().asm() + ('i' if self.children[0].type == Int() else 'f') + 'neq'


class REL_GT(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        return super().asm() + ('i' if self.children[0].type == Int() else 'f') + 'gt'


class REL_LT(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        return super().asm() + ('i' if self.children[0].type == Int() else 'f') + 'lt'


class REL_GTE(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>='

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        return super().asm() + ('i' if self.children[0].type == Int() else 'f') + 'gte'


class REL_LTE(REL_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<='

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        return super().asm() + ('i' if self.children[0].type == Int() else 'f') + 'lte'


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

    def copy(self) -> TL_FT_BIN_OP:
        new = type(self)(self.ln,self.get_lhs().copy(),self.get_rhs().copy(),self.interval.lb,self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


class TL_UNTIL(TL_FT_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'U'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'until n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + ''


class TL_RELEASE(TL_FT_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'R'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'release n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + ''


class TL_FT_UNARY_OP(TL_FT_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def get_operand(self) -> AST:
        return self.children[0]

    def copy(self) -> TL_FT_UNARY_OP:
        new = type(self)(self.ln,self.get_operand().copy(),self.interval.lb,self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


class TL_GLOBAL(TL_FT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'G'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'global n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + ''


class TL_FUTURE(TL_FT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'F'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'future n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + ''


class TL_PT_BIN_OP(TL_PT_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, [lhs, rhs], l, u)

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def copy(self) -> TL_PT_BIN_OP:
        new = type(self)(self.ln,self.get_lhs().copy(),self.get_rhs().copy(),self.interval.lb,self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


class TL_SINCE(TL_PT_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'S'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'since n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + ''


class TL_PT_UNARY_OP(TL_PT_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.interval = Interval(lb=l,ub=u)

    def get_operand(self) -> AST:
        return self.children[0]

    def copy(self) -> TL_PT_UNARY_OP:
        new = type(self)(self.ln,self.get_operand().copy(),self.interval.lb,self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


class TL_HISTORICAL(TL_PT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'H'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'his n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + ''


class TL_ONCE(TL_PT_UNARY_OP):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'O'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'once n' + str(operand.tlid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + ''


class LOG_OP(TL_EXPR):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln,c)

    def copy(self) -> LOG_OP:
        new = type(self)(self.ln,[c.copy() for c in self.children])
        self.copy_attrs(new)
        return new


class LOG_OR(LOG_OP):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.name: str = '||'

    def __str__(self) -> str:
        s: str = ''
        for arg in self.children:
            s += str(arg) + '||'
        return s[:-2]

    def asm(self) -> str:
        s: str = super().asm() + 'or'
        for c in self.children:
            s += ' n' + str(c.tlid)
        return s + ''


class LOG_AND(LOG_OP):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.name: str = '&&'

    def __str__(self) -> str:
        s: str = ''
        for arg in self.children:
            s += str(arg) + '&&'
        return s[:-2]

    def asm(self) -> str:
        s: str = super().asm() + 'and'
        for c in self.children:
            s += ' n' + str(c.tlid)
        return s + ''


class LOG_BIN_OP(LOG_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln,[lhs, rhs])
        self.bpd = min(lhs.bpd, rhs.bpd)
        self.wpd = max(lhs.wpd, rhs.wpd)

    def get_lhs(self) -> AST:
        return self.children[0]

    def get_rhs(self) -> AST:
        return self.children[1]

    def copy(self) -> LOG_BIN_OP:
        new = type(self)(self.ln,self.get_lhs().copy(),self.get_rhs().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


class LOG_BIN_OR(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '||'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'or n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ''


class LOG_BIN_AND(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '&&'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'and n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ''


class LOG_XOR(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '^^'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'xor n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ''


class LOG_IMPL(LOG_BIN_OP):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '->'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'impl n' + str(lhs.tlid) + ' n' + str(rhs.tlid) + ''


class LOG_UNARY_OP(LOG_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln,[o])
        self.bpd = o.bpd
        self.wpd = o.wpd

    def get_operand(self) -> AST:
        return self.children[0]

    def copy(self) -> LOG_UNARY_OP:
        new = type(self)(self.ln,self.get_operand().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class LOG_NEG(LOG_UNARY_OP):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln, o)
        self.name: str = '!'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'not n' + str(operand.tlid) + ''


class SPEC(TL_EXPR):
    
    def __init__(self, ln: int, lbl: str, f: int, e: AST) -> None:
        super().__init__(ln, [e])
        self.name: str = lbl
        self.fnum: int = f

    def get_expr(self) -> AST:
        return self.children[0]

    def copy(self) -> SPEC:
        new: SPEC = SPEC(self.ln, self.name, self.fnum, self.get_expr().copy())
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return (self.name + ': ' if self.name != '' else '')  + str(self.children[0])

    def asm(self) -> str:
        top: AST = self.children[0]
        return super().asm() + 'end n' + str(top.tlid) + ' f' + str(self.fnum) + ''


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
            ret += str(s) + ''
        ret = ret[:-1]
        return ret

    def asm(self) -> str:
        return super().asm() + 'endsequence'

