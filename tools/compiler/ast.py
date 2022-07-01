from __future__ import annotations
from collections.abc import Callable
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


class AST():

    def __init__(self, c: list[AST]) -> None:
        self.nid: int = -1
        self.id: str = str(self.nid)
        self.scq_size: int = -1
        self.name: str = ''
        self.bpd: int = 0
        self.wpd: int = 0
        self._type: Type = Type.NONE
        self.children: list[AST] = []

        child: AST
        for child in c:
            self.children.append(child)

    def asm(self) -> str:
        return "n"+str(self.nid)+": "


class EXPR(AST):

    def __init__(self, c: list[AST]) -> None:
        super().__init__(c)


class LIT(EXPR):  

    def __init__(self) -> None:
        super().__init__([])


class CONST(LIT):

    def __init__(self) -> None:
        super().__init__()
        self.bpd: int = 0
        self.wpd: int = 0


class BOOL(CONST):
    
    def __init__(self, v: bool) -> None:
        super().__init__()
        self._type = Type.BOOL
        self.val: bool = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name


class INT(CONST):
    
    def __init__(self, v: int) -> None:
        super().__init__()
        self._type = Type.INT
        self.val: int = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name


class FLOAT(CONST):
    
    def __init__(self, v: float) -> None:
        super().__init__()
        self._type = Type.FLOAT
        self.val: float = v
        self.name = str(v)

    def __str__(self) -> str:
        return self.name


class VAR(LIT):
    
    def __init__(self, n: str, t: Type) -> None:
        super().__init__()
        self.name: str = n
        self._type: Type = t
        self.sid = -1

    def __str__(self) -> str:
        return self.name

    def asm(self, a: int) -> str:
        return 'a' + str(a) + ': ' + to_str(self._type) + ' == ' + '1 s' + str(self.sid) + '\n'


class ATOM(LIT):
    
    def __init__(self, n: str, a: int) -> None:
        super().__init__()
        self._type: Type = Type.BOOL
        self.bpd: int = 0
        self.wpd: int = 0
        self.name: str = n
        self.aid: int = a

    def __str__(self) -> str:
        return self.name

    def asm(self) -> str:
        return super().asm() + 'load ' + self.name + '\n'


class LOG_BIN_OP(EXPR):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__([lhs, rhs])
        self.bpd = min(lhs.bpd, rhs.bpd)
        self.wpd = max(lhs.wpd, rhs.wpd)

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}({self.children[1]!s})'


class REL_OP(EXPR):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__([lhs, rhs])

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


class TL_BIN_OP(EXPR):

    def __init__(self, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__([lhs, rhs])
        self.interval = Interval(lb=l,ub=u)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def __str__(self) -> str:
        return f'({self.children[0]!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})'


class LOG_UNARY_OP(EXPR):

    def __init__(self, o: EXPR):
        super().__init__([o])
        self.bpd = o.bpd
        self.wpd = o.wpd

    def __str__(self) -> str:
        return f'{self.name!s}({self.children[0]!s})'


class TL_UNARY_OP(EXPR):

    def __init__(self, o: EXPR, l: int, u: int) -> None:
        super().__init__([o])
        self.interval = Interval(lb=l,ub=u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.children[0]!s})'


class TERNARY_OP(EXPR):

    def __init__(self, arg1: EXPR , arg2: EXPR, arg3: EXPR) -> None:
        super().__init__([arg1,arg2,arg3])
        self.name: str = 'ite'

    def __str__(self) -> str:
        arg1: AST = self.children[0]
        arg2: AST = self.children[1]
        arg3: AST = self.children[2]
        return '(' + str(arg1) + ')?(' + str(arg2) + '):(' + str(arg3) + ')'


class LOG_OR(LOG_BIN_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '||'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'or ' + lhs.id + ' ' + rhs.id + '\n'


class LOG_AND(LOG_BIN_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '||'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'and ' + lhs.id + ' ' + rhs.id + '\n'


class REL_EQ(REL_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '=='

    def __str__(self) -> str:
        return super().__str__()


class REL_NEQ(REL_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '!='

    def __str__(self) -> str:
        return super().__str__()


class REL_GT(REL_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '>'

    def __str__(self) -> str:
        return super().__str__()


class REL_LT(REL_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '<'

    def __str__(self) -> str:
        return super().__str__()


class REL_GTE(REL_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '>='

    def __str__(self) -> str:
        return super().__str__()


class REL_LTE(REL_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR) -> None:
        super().__init__(lhs, rhs)
        self.name: str = '<='

    def __str__(self) -> str:
        return super().__str__()


class TL_UNTIL(TL_BIN_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(lhs, rhs, l, u)
        self.name: str = 'U'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'until ' + lhs.id + ' ' + rhs.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_RELEASE(TL_BIN_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(lhs, rhs, l, u)
        self.name: str = 'R'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'release ' + lhs.id + ' ' + rhs.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_SINCE(TL_BIN_OP):

    def __init__(self, lhs: EXPR, rhs: EXPR, l: int, u: int) -> None:
        super().__init__(lhs, rhs, l, u)
        self.name: str = 'S'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        lhs: AST = self.children[0]
        rhs: AST = self.children[1]
        return super().asm() + 'since ' + lhs.id + ' ' + rhs.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class LOG_NEG(LOG_UNARY_OP):

    def __init__(self, o: EXPR):
        super().__init__(o)
        self.name: str = '!'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'not ' + operand.id


class TL_GLOBAL(TL_UNARY_OP):

    def __init__(self, o: EXPR, l: int, u: int) -> None:
        super().__init__(o, l, u)
        self.name: str = 'G'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'global ' + operand.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_FUTURE(TL_UNARY_OP):

    def __init__(self, o: EXPR, l: int, u: int) -> None:
        super().__init__(o, l, u)
        self.name: str = 'F'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'future ' + operand.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_HISTORICAL(TL_UNARY_OP):

    def __init__(self, o: EXPR, l: int, u: int) -> None:
        super().__init__(o, l, u)
        self.name: str = 'H'

    def __str__(self) -> str:
        return super().__str__()

    def asm(self) -> str:
        operand: AST = self.children[0]
        return super().asm() + 'his n' + operand.id + ' ' + \
                str(self.interval.lb) + ' ' + str(self.interval.ub) + '\n'


class TL_ONCE(TL_UNARY_OP):
    pass


class SPEC(AST):
    
    def __init__(self, lbl: str, f: int, e: EXPR) -> None:
        super().__init__([e])
        self.name: str = lbl
        self.fnum = f

    def __str__(self) -> str:
        return self.name + ': ' + str(self.children[0])

    def asm(self) -> str:
        top: AST = self.children[0]
        return super().asm() + 'end ' + top.id + ' ' + str(self.fnum) + '\n'


class PROGRAM(AST):

    def __init__(self, s: dict[tuple[int,str],SPEC], o: dict[str,int]) -> None:
        super().__init__(list(s.values()))
        self.order = o

    def __str__(self) -> str:
        ret: str = ''
        s: AST
        for s in self.children:
            ret += str(s) + '\n'
        return ret

    def asm(self) -> str:
        return super().asm() + 'end sequence'


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

        if isinstance(a,CONST):
            a.id = a.name
            return
        
        # assign nid to nodes we have not seen
        # by default, nid = -1
        if a.nid < 0:
            a.nid = n
            a.id = 'n'+str(n)
            n += 1

    postorder(a,assign_nid_util)


def assign_sid(a: PROGRAM) -> None:
    order: dict[str,int] = a.order

    def assign_sid_util(a: AST) -> None:
        nonlocal order

        if isinstance(a,VAR): 
            b = cast(VAR,a)
            if b.name in list(order):
                b.sid = order[b.name]
            else:
                raise RuntimeError('Referenced signal not defined')

    postorder(a,assign_sid_util)


def type_check(a: AST) -> bool:
    status: bool = True

    def type_check_util(a: AST) -> None: # TODO error messages
        nonlocal status

        if isinstance(a,LIT) or isinstance(a,PROGRAM):
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


def gen_atomic_asm(a: PROGRAM) -> str:
    if not type_check(a):
        return ''

    s: str = ''
    visited: dict[int,ATOM] = {}
    a_num: int = 0

    def gen_atomic_asm_util(a: AST) -> None:
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
                    s += tmp.asm(a_num)
                    visited[i] = ATOM('a'+str(a_num),a_num)
                    a.children[c] = visited[i]
                    a_num += 1
            elif isinstance(child,VAR): 
                if i in list(visited):
                    a.children[c] = visited[i]
                else:
                    tmp = cast(VAR,child)
                    s += tmp.asm(a_num)
                    tmp = ATOM('a'+str(a_num),a_num)
                    visited[i] = tmp
                    a.children[c] = tmp
                    a_num += 1

    preorder(a,gen_atomic_asm_util)
    return s


def compute_scq_size(a: AST) -> None:
    
    def compute_scq_size_util(a: AST) -> None:
        if isinstance(a, PROGRAM):
            # all SPEC scq_size = 1
            for c in a.children:
                c.scq_size = 1
            return

        wpd: int = 0
        for c in a.children:
            if c.wpd > wpd:
                wpd = c.wpd

        for c in a.children:
            c.scq_size = max(wpd-c.bpd,0)+3 # +3 b/c of some bug -- ask Brian

    preorder(a,compute_scq_size_util)


def gen_scq_assembly(a: AST) -> str:
    s: str = ''
    pos: int = 0

    compute_scq_size(a)

    def gen_scq_assembly_util(a: AST) -> None:
        nonlocal s
        nonlocal pos

        if isinstance(a,PROGRAM) or isinstance(a,CONST):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        s += str(start_pos) + ' ' + str(end_pos) + '\n'

    postorder(a,gen_scq_assembly_util)
    return s


def gen_assembly(a: PROGRAM) -> list[str]:
    if not type_check(a):
        return ['','n0: end sequence','n0: end sequence']

    assign_sid(a)
    optimize_cse(a)

    atomic_asm: str = gen_atomic_asm(a)

    assign_nid(a)

    visited: list[int] = []
    ft_asm: str = ''

    def gen_assembly_util(a: AST) -> None:
        nonlocal ft_asm
        nonlocal visited

        if isinstance(a, VAR) or isinstance(a, REL_OP):
            raise RuntimeError('Atomics not resolved; call \'gen_atomic_eval\' before \'gen_assembly\'')

        if isinstance(a,CONST):
            return

        if not a.nid in visited:
            ft_asm += a.asm()
            visited.append(a.nid)

    postorder(a,gen_assembly_util)

    scq_asm = gen_scq_assembly(a)

    return [atomic_asm,ft_asm,'n0: end sequence',scq_asm]


