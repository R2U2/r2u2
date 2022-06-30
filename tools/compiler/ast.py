from __future__ import annotations
from collections.abc import Callable
from dataclasses import dataclass, field, InitVar
from enum import Enum
from typing import Any, NamedTuple, cast

class Type(Enum):
    NONE = 0
    BOOL = 1
    INT = 2
    FLOAT = 3

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

# kw_only option gets rid of issues of ordering params with default/no defaults 
# i.e., python requires all values with defaults have kw and all kw params come first, 
# so there's trouble if a param without a default or kw comes after one with it

@dataclass(kw_only=True)
class AST():
    lineno: int = 0
    children: list[AST] = field(default_factory=list)
    name: str = field(init=False, default='')
    nid: int = field(init=False, default=-1)
    scq_size: int = field(init=False, default=-1)
    size: int = field(init=False, default=-1)

    def gen_assembly(self) -> str:
        return "s"+str(self.nid)+": "


@dataclass(kw_only=True)
class EXPR(AST):
    children: list[EXPR] = field(default_factory=list)
    _type: Type = field(init=False, default=Type.NONE)
    bpd: int = field(init=False)
    wpd: int = field(init=False)


@dataclass(kw_only=True)
class LIT(EXPR):
    pass


@dataclass(kw_only=True)
class CONST(LIT):
    bpd: int = 0
    wpd: int = 0
    size: int = 1


@dataclass(kw_only=True)
class BOOL(CONST):
    val: bool
    _type = Type.BOOL

    def __post_init__(self):
        self.name = str(self.val)

    def __str__(self) -> str:
        return str(self.val)


@dataclass(kw_only=True)
class INT(CONST):
    val: int
    _type = Type.INT

    def __post_init__(self):
        self.name = str(self.val)

    def __str__(self) -> str:
        return str(self.val)


@dataclass(kw_only=True)
class FLOAT(CONST):
    val: float
    _type = Type.FLOAT

    def __post_init__(self):
        self.name = str(self.val)

    def __str__(self) -> str:
        return str(self.val)


@dataclass(kw_only=True)
class VAR(LIT):
    _type: Type = field(init=True)
    name: str = ''
    size: int = 1
    sid: int = field(init=False, default=-1)

    def __post_init__(self):
        self.bpd = 1
        self.wpd = 1

    def __str__(self) -> str:
        return self.name

    def gen_assembly(self, a: int) -> str:
        return 'a' + str(a) + ': ' + to_str(self._type) + ' == s' + str(self.sid) + ' 1\n'


@dataclass(kw_only=True)
class ATOM(LIT):
    _type: Type = Type.BOOL
    name: str = ''
    size: int = 1

    def __post_init__(self):
        self.bpd = 1
        self.wpd = 1

    def __str__(self) -> str:
        return self.name

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'load ' + self.name + '\n'


@dataclass(kw_only=True)
class TERNARY_OP(EXPR):
    arg1: InitVar[EXPR]
    arg2: InitVar[EXPR]
    arg3: InitVar[EXPR]
    _type = Type.NONE
    name: str = 'ite' 

    def __post_init__(self, arg1, arg2, arg3):
        self.children = [arg1,arg2,arg3]
        self.size = 1 + arg1.size + arg2.size + arg3.size

    def __str__(self) -> str:
        return '(' + str(self.children[0]) + ')?(' + str(self.children[1]) + '):(' + str(self.children[2]) + ')'


@dataclass(kw_only=True)
class BIN_OP(EXPR):
    lhs: InitVar[EXPR]
    rhs: InitVar[EXPR]
    _type = Type.NONE

    def __post_init__(self, lhs, rhs):
        self.children = [lhs,rhs]
        self.size = 1 + lhs.size + rhs.size


@dataclass(kw_only=True)
class UNARY_OP(EXPR):
    operand: InitVar[EXPR]
    _type = Type.NONE

    def __post_init__(self, operand):
        self.children = [operand]
        self.size = 1 + operand.size


@dataclass(kw_only=True)
class LOG_BIN_OP(BIN_OP):

    def __post_init__(self, lhs, rhs):
        super().__post_init__(lhs, rhs)
        self.bpd = min(lhs.bpd, rhs.bpd)
        self.wpd = max(lhs.wpd, rhs.wpd)

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


@dataclass(kw_only=True)
class REL_OP(BIN_OP):

    def __post_init__(self, lhs, rhs):
        super().__post_init__(lhs, rhs)
        self.bpd = min(lhs.bpd, rhs.bpd)
        self.wpd = max(lhs.wpd, rhs.wpd)

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'

    def gen_assembly(self, a: int) -> str:
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

        return 'a' + str(a) + ': ' + to_str(self.children[0]._type) + ' ' + self.name + ' ' + a1 + ' ' + a2 + '\n'


@dataclass(kw_only=True)
class TL_BIN_OP(BIN_OP):
    interval: Interval

    def __post_init__(self, lhs, rhs):
        super().__post_init__(lhs, rhs)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


@dataclass(kw_only=True)
class LOG_UNARY_OP(UNARY_OP):

    def __post_init__(self, operand):
        super().__post_init__(operand)
        self.bpd = operand.bpd
        self.wpd = operand.wpd

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


@dataclass(kw_only=True)
class TL_UNARY_OP(UNARY_OP):
    interval: Interval

    def __post_init__(self, operand):
        super().__post_init__(operand)
        self.bpd = operand.bpd + self.interval.lb
        self.wpd = operand.wpd + self.interval.ub

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


@dataclass(kw_only=True)
class LOG_OR(LOG_BIN_OP):
    name: str = '||'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'or ' + str(self.children[0].nid) + ' ' + str(self.children[1].nid) + '\n'


@dataclass(kw_only=True)
class LOG_AND(LOG_BIN_OP):
    name: str = '&&'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'and ' + str(self.children[0].nid) + ' ' + str(self.children[1].nid) + '\n'


@dataclass(kw_only=True)
class REL_EQ(REL_OP):
    name: str = '=='


@dataclass(kw_only=True)
class REL_NEQ(REL_OP):
    name: str = '!='


@dataclass(kw_only=True)
class REL_GT(REL_OP):
    name: str = '>'


@dataclass(kw_only=True)
class REL_LT(REL_OP):
    name: str = '<'


@dataclass(kw_only=True)
class REL_GTE(REL_OP):
    name: str = '>='


@dataclass(kw_only=True)
class REL_LTE(REL_OP):
    name: str = '<='


@dataclass(kw_only=True)
class TL_UNTIL(TL_BIN_OP):
    name: str = 'U'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'until ' + str(self.children[0].nid) + ' ' + str(self.children[1].nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_RELEASE(TL_BIN_OP):
    name: str = 'R'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'release ' + str(self.children[0].nid) + ' ' + str(self.children[1].nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_SINCE(TL_BIN_OP):
    name: str = 'S'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'since ' + str(self.children[0].nid) + ' ' + str(self.children[1].nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class LOG_NEG(LOG_UNARY_OP):
    name: str = '!'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'not ' + str(self.children[0].nid)


@dataclass(kw_only=True)
class ARITH_NEG(UNARY_OP):
    name: str = '-'


@dataclass(kw_only=True)
class TL_GLOBAL(TL_UNARY_OP):
    name: str = 'G'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'boxdot ' + str(self.children[0].nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_FUTURE(TL_UNARY_OP):
    name: str = 'F'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'future ' + str(self.children[0].nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_HISTORICAL(TL_UNARY_OP):
    name: str = 'H'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'his ' + str(self.children[0].nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_ONCE(TL_UNARY_OP):
    pass


@dataclass(kw_only=True)
class SPEC(AST):
    child: InitVar[EXPR]
    name: str = ''

    def __post_init__(self, child):
        self.children = [child]
        self.size = 1 + child.size

    def __str__(self) -> str:
        return self.name + ': ' + str(self.children[0])

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'end ' + str(self.children[0].nid) + '\n'


@dataclass(kw_only=True)
class PROGRAM(AST):
    vars: dict[str,Type]
    specs: dict[tuple[int,str],SPEC] # (spec_num, label) -> spec
    order: dict[str,int]
    name: str = 'Program'

    def __post_init__(self):
        self.size = 1
        s: SPEC
        for s in self.specs.values():
            self.children.append(s)
            self.size += s.size

    def __str__(self) -> str:
        ret: str = ''
        s: SPEC
        for s in self.specs.values():
            ret += str(s) + '\n'
        return ret

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'end sequence'


def postorder(a: AST, func: Callable[[AST],Any]) -> None:
    c: AST
    for c in a.children:
        postorder(c,func)
    func(a)


def preorder(a: AST, func: Callable[[AST],Any]) -> None:
    func(a)
    c: AST
    for c in a.children:
        preorder(c,func)


def assign_nid(a: AST) -> None:
    n = 0

    def assign_nid_util(a: AST) -> None:
        nonlocal n
        if a.nid < 0:
            a.nid = n
            n += 1

    postorder(a,assign_nid_util)


def assign_sid(a: PROGRAM) -> None:
    s_num: dict[str,int] = a.order
    sigs: list[str] = list(s_num)

    def assign_sid_util(a: AST) -> None:
        nonlocal s_num
        nonlocal sigs
        if isinstance(a,VAR): 
            b = cast(VAR,a)
            if b.name in sigs:
                b.sid = s_num[b.name]
            else:
                raise RuntimeError('Referenced signal not defined')

    postorder(a,assign_sid_util)


def type_check(a: AST) -> bool:
    status: bool = True

    def type_check_util(a: AST) -> None: # TODO error messages
        nonlocal status
        if isinstance(a,VAR) or isinstance(a,CONST) or isinstance(a,PROGRAM):
            pass

        elif isinstance(a,SPEC):
            child = cast(EXPR,a.children[0])
            if not child._type == Type.BOOL:
                status = False
        elif isinstance(a,REL_OP):
            # both operands must be literals of same type
            lhs = a.children[0]
            rhs = a.children[1]
            if not isinstance(lhs,LIT) and isinstance(rhs,LIT):
                status = False
            if not lhs._type == rhs._type:
                status = False
            a._type = Type.BOOL
        elif isinstance(a,TERNARY_OP):
            arg1 = a.children[0]
            arg2 = a.children[1]
            arg3 = a.children[2]
            status = status and arg1._type == arg2._type == arg3._type
            a._type = Type.BOOL
        elif isinstance(a,TL_BIN_OP):
            lhs = a.children[0]
            rhs = a.children[1]
            status = status and lhs._type == Type.BOOL
            status = status and rhs._type == Type.BOOL
            status = status and a.interval.lb <= a.interval.ub
            a._type = Type.BOOL
        elif isinstance(a,TL_UNARY_OP):
            operand = a.children[0]
            status = status and operand._type == Type.BOOL
            status = status and a.interval.lb <= a.interval.ub
            a._type = Type.BOOL
        elif isinstance(a,LOG_BIN_OP):
            lhs = a.children[0]
            rhs = a.children[1]
            status = status and lhs._type == Type.BOOL
            status = status and rhs._type == Type.BOOL
            a._type = Type.BOOL
        elif isinstance(a,LOG_UNARY_OP):
            operand = a.children[0]
            status = status and operand._type == Type.BOOL
            a._type = Type.BOOL
        else:
            status = False

    postorder(a,type_check_util)
    return status


def optimize_cse(a: PROGRAM) -> None:
    S: dict[str,AST] = {}
    
    def optimize_cse(a: AST) -> None:
        nonlocal S
        c: int
        i: str
        for c in range(0,len(a.children)):
            child = a.children[c]
            i = str(child)

            if i in list(S):
                a.children[c] = S[i]
            else:
                S[i] = a.children[c]
            
    postorder(a,optimize_cse)


def gen_atomic_eval(a: PROGRAM) -> str:
    s: str = ''
    visited: dict[int,ATOM] = {}
    a_num: int = 0
    assign_sid(a)

    def gen_atomic_eval_util(a: AST) -> None:
        nonlocal s
        nonlocal visited
        nonlocal a_num

        c: int
        for c in range(0,len(a.children)):
            child = a.children[c]
            i = id(child)

            if isinstance(a,REL_OP):
                return

            if isinstance(child,REL_OP):
                if i in list(visited):
                    a.children[c] = visited[i]
                else:
                    tmp = cast(REL_OP,child)
                    s += tmp.gen_assembly(a_num)
                    tmp = ATOM(lineno=a.lineno, name='a'+str(a_num))
                    visited[i] = tmp
                    a.children[c] = tmp
                    a_num += 1
            elif isinstance(child,VAR): 
                if i in list(visited):
                    a.children[c] = visited[i]
                else:
                    tmp = cast(VAR,child)
                    s += tmp.gen_assembly(a_num)
                    tmp = ATOM(lineno=a.lineno, name='a'+str(a_num))
                    visited[i] = tmp
                    a.children[c] = tmp
                    a_num += 1

    preorder(a,gen_atomic_eval_util)
    return s


def gen_assembly(a: PROGRAM) -> str:
    if not type_check(a):
        return 's0: end sequence'

    optimize_cse(a)
    print(gen_atomic_eval(a))
    assign_nid(a)
    visited: list[int] = []
    s: str = ''

    def gen_assembly_util(a: AST) -> None:
        nonlocal s
        nonlocal visited
        if not a.nid in visited:
            s += a.gen_assembly()
            visited.append(a.nid)

    postorder(a,gen_assembly_util)
    return s



def compute_scq_size(a: AST) -> None:
    pass