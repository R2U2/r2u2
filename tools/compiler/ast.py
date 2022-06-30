from collections.abc import Callable
from dataclasses import dataclass, field
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
    lineno: int
    name: str = field(init=False)
    nid: int = field(init=False)
    scq_size: int = field(init=False)
    size: int = field(init=False)

    def gen_assembly(self) -> str:
        return "s"+str(self.nid)+": "


@dataclass(kw_only=True)
class EXPR(AST):
    _type: Type = field(init=False)
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
    sid: int = field(init=False)

    def __post_init__(self):
        self.bpd = 1
        self.wpd = 1

    def __str__(self) -> str:
        return self.name

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'load ' + self.name + '\n'


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
    arg1: EXPR
    arg2: EXPR
    arg3: EXPR
    _type = Type.NONE
    name: str = 'ite'

    def __str__(self) -> str:
        return '(' + str(self.arg1) + ')?(' + str(self.arg2) + '):(' + str(self.arg3) + ')' 

    def __post_init__(self):
        self.size = 1 + self.arg1.size + self.arg2.size + self.arg3.size


@dataclass(kw_only=True)
class BIN_OP(EXPR):
    lhs: EXPR
    rhs: EXPR
    _type = Type.NONE

    def __post_init__(self):
        self.size = 1 + self.lhs.size + self.rhs.size


@dataclass(kw_only=True)
class UNARY_OP(EXPR):
    operand: EXPR
    _type = Type.NONE

    def __post_init__(self):
        self.size = 1 + self.operand.size


@dataclass(kw_only=True)
class LOG_BIN_OP(BIN_OP):

    def __post_init__(self):
        super().__post_init__()
        self.bpd = min(self.lhs.bpd, self.rhs.bpd)
        self.wpd = max(self.lhs.wpd, self.rhs.wpd)

    def __str__(self) -> str:
        return f'({self.lhs!s}){self.name!s}({self.rhs!s})'


@dataclass(kw_only=True)
class REL_OP(BIN_OP):
    lhs: LIT
    rhs: LIT

    def __post_init__(self):
        super().__post_init__()
        self.bpd = min(self.lhs.bpd, self.rhs.bpd)
        self.wpd = max(self.lhs.wpd, self.rhs.wpd)

    def __str__(self) -> str:
        return f'({self.lhs!s}){self.name!s}({self.rhs!s})'

    def gen_assembly(self, a: int) -> str:
        a1: str
        a2: str

        if isinstance(self.lhs,CONST):
            a1 = self.lhs.name
        else:
            tmp = cast(VAR,self.lhs)
            a1 = 's'+str(tmp.sid)

        if isinstance(self.rhs,CONST):
            a2 = self.rhs.name
        else:
            tmp = cast(VAR,self.rhs)
            a2 = 's'+str(tmp.sid)

        return 'a' + str(a) + ': ' + to_str(self.lhs._type) + ' ' + self.name + ' ' + \
            a1 + ' ' + a2 + '\n'


@dataclass(kw_only=True)
class TL_BIN_OP(BIN_OP):
    interval: Interval

    def __post_init__(self):
        super().__post_init__()
        self.bpd = min(self.lhs.bpd, self.rhs.bpd) + self.interval.lb
        self.wpd = max(self.lhs.wpd, self.rhs.wpd) + self.interval.ub

    def __str__(self) -> str:
        return f'({self.lhs!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.rhs!s})'


@dataclass(kw_only=True)
class LOG_UNARY_OP(UNARY_OP):

    def __post_init__(self):
        super().__post_init__()
        self.bpd = self.operand.bpd
        self.wpd = self.operand.wpd

    def __str__(self) -> str:
        return f'{self.name!s}({self.operand!s})'


@dataclass(kw_only=True)
class TL_UNARY_OP(UNARY_OP):
    interval: Interval

    def __post_init__(self):
        super().__post_init__()
        self.bpd = self.operand.bpd + self.interval.lb
        self.wpd = self.operand.wpd + self.interval.ub

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.operand!s})'


@dataclass(kw_only=True)
class LOG_OR(LOG_BIN_OP):
    name: str = '||'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'or ' + str(self.lhs.nid) + ' ' + str(self.rhs.nid) + '\n'


@dataclass(kw_only=True)
class LOG_AND(LOG_BIN_OP):
    name: str = '&&'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'and ' + str(self.lhs.nid) + ' ' + str(self.rhs.nid) + '\n'


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
        return super().gen_assembly() + 'until ' + str(self.lhs.nid) + ' ' + str(self.rhs.nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_RELEASE(TL_BIN_OP):
    name: str = 'R'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'release ' + str(self.lhs.nid) + ' ' + str(self.rhs.nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_SINCE(TL_BIN_OP):
    name: str = 'S'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'since ' + str(self.lhs.nid) + ' ' + str(self.rhs.nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class LOG_NEG(LOG_UNARY_OP):
    name: str = '!'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'not ' + str(self.operand.nid)


@dataclass(kw_only=True)
class ARITH_NEG(UNARY_OP):
    name: str = '-'


@dataclass(kw_only=True)
class TL_GLOBAL(TL_UNARY_OP):
    name: str = 'G'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'boxdot ' + str(self.operand.nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_FUTURE(TL_UNARY_OP):
    name: str = 'F'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'future ' + str(self.operand.nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_HISTORICAL(TL_UNARY_OP):
    name: str = 'H'

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'his ' + str(self.operand.nid) + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


@dataclass(kw_only=True)
class TL_ONCE(TL_UNARY_OP):
    pass


@dataclass(kw_only=True)
class SPEC(AST):
    child: EXPR
    name: str = ''

    def __post_init__(self):
        self.size = 1 + self.child.size

    def __str__(self) -> str:
        return self.name + ': ' + str(self.child)

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'end ' + str(self.child.nid) + '\n'


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
            self.size += s.size

    def __str__(self) -> str:
        ret: str = ''
        s: SPEC
        for s in self.specs.values():
            ret += str(s) + '\n'
        return ret

    def gen_assembly(self) -> str:
        return super().gen_assembly() + 'end sequence'


def postorder(a: AST, func: Callable[[AST],Any]) -> Any:
    if isinstance(a,PROGRAM):
        b = cast(PROGRAM,a)
        s: SPEC
        for s in b.specs.values():
            postorder(s,func)
    elif isinstance(a,SPEC):
        b = cast(SPEC,a)
        postorder(b.child,func)
    elif isinstance(a,TERNARY_OP):
        b = cast(TERNARY_OP,a)
        postorder(b.arg1,func)
        postorder(b.arg2,func)
        postorder(b.arg3,func)
    elif isinstance(a,BIN_OP):
        b = cast(BIN_OP,a)
        postorder(b.lhs,func)
        postorder(b.rhs,func)
    elif isinstance(a,UNARY_OP):
        b = cast(UNARY_OP,a)
        postorder(b.operand,func)
    
    return func(a)


def preorder(a: AST, func: Callable[[AST],Any]) -> Any:
    ret = func(a)

    if isinstance(a,PROGRAM):
        b = cast(PROGRAM,a)
        s: SPEC
        for s in b.specs.values():
            preorder(s,func)
    elif isinstance(a,SPEC):
        b = cast(SPEC,a)
        preorder(b.child,func)
    elif isinstance(a,TERNARY_OP):
        b = cast(TERNARY_OP,a)
        preorder(b.arg1,func)
        preorder(b.arg2,func)
        preorder(b.arg3,func)
    elif isinstance(a,BIN_OP):
        b = cast(BIN_OP,a)
        preorder(b.lhs,func)
        preorder(b.rhs,func)
    elif isinstance(a,UNARY_OP):
        b = cast(UNARY_OP,a)
        preorder(b.operand,func)
    
    return ret


def assign_nid(a: AST) -> None:
    n = 0
    def assign_nid_util(a: AST) -> None:
        nonlocal n
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
            b = cast(SPEC,a)
            if not b.child._type == Type.BOOL:
                status = False
        elif isinstance(a,REL_OP):
            # both operands must be literals of same type
            b = cast(REL_OP,a)
            if not isinstance(b.lhs,LIT) and isinstance(b.rhs,LIT):
                status = False
            if not b.lhs._type == b.rhs._type:
                status = False
            b._type = Type.BOOL
        elif isinstance(a,TERNARY_OP):
            b = cast(TERNARY_OP,a)
            status = status and type(b.arg1) == type(b.arg2) == type(b.arg3)
            b._type = Type.BOOL
        elif isinstance(a,TL_BIN_OP):
            b = cast(TL_BIN_OP,a)
            status = status and b.lhs._type == Type.BOOL
            status = status and b.rhs._type == Type.BOOL
            status = status and b.interval.lb <= b.interval.ub
            b._type = Type.BOOL
        elif isinstance(a,TL_UNARY_OP):
            b = cast(TL_UNARY_OP,a)
            status = status and b.operand._type == Type.BOOL
            status = status and b.interval.lb <= b.interval.ub
            b._type = Type.BOOL
        elif isinstance(a,LOG_BIN_OP):
            b = cast(LOG_BIN_OP,a)
            status = status and b.lhs._type == Type.BOOL
            status = status and b.rhs._type == Type.BOOL
            b._type = Type.BOOL
        elif isinstance(a,LOG_UNARY_OP):
            b = cast(LOG_UNARY_OP,a)
            status = status and b.operand._type == Type.BOOL
            b._type = Type.BOOL
        else:
            status = False

    postorder(a,type_check_util)
    return status


def gen_atomic_eval(a: PROGRAM) -> str:
    s: str = ''
    a_num: int = 0
    assign_sid(a)

    def gen_atomic_eval_util(a: AST) -> None:
        nonlocal s
        nonlocal a_num
        if isinstance(a,TERNARY_OP):
            b = cast(TERNARY_OP,a)

            if isinstance(b.arg1,REL_OP):
                b.arg1 = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
            elif isinstance(b.arg1,VAR):
                b.arg1 = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1

            if isinstance(b.arg2,REL_OP):
                b.arg2 = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
            elif isinstance(b.arg2,VAR):
                b.arg2 = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1

            if isinstance(b.arg3,REL_OP):
                b.arg3 = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
            elif isinstance(b.arg3,VAR):
                b.arg3 = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
        elif isinstance(a,BIN_OP):
            b = cast(BIN_OP,a)

            if isinstance(b.lhs,REL_OP):
                b.lhs = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
            elif isinstance(b.lhs,VAR):
                b.lhs = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1

            if isinstance(b.rhs,REL_OP):
                print(b.rhs.gen_assembly(a_num))
                b.rhs = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
            elif isinstance(b.rhs,VAR):
                b.rhs = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
        elif isinstance(a,UNARY_OP):
            b = cast(UNARY_OP,a)

            if isinstance(b.operand,REL_OP):
                b.operand = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1
            elif isinstance(b.operand,VAR):
                b.operand = ATOM(lineno=a.lineno, name='a'+str(a_num))
                a_num += 1

    preorder(a,gen_atomic_eval_util)
    return ''


def gen_assembly(a: PROGRAM) -> str:
    if not type_check(a):
        return 's0: end sequence'

    gen_atomic_eval(a)
    assign_nid(a)
    s: str = ''

    def gen_assembly_util(a: AST) -> None:
        nonlocal s
        s += a.gen_assembly()

    postorder(a,gen_assembly_util)
    return s



def compute_scq_size(a: AST) -> None:
    pass