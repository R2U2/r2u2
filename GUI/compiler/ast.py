from __future__ import annotations
from copy import deepcopy
from typing import Any, Callable, NamedTuple, NewType, cast
from logging import getLogger

from .logger import *
from .type import *

logger = getLogger(STANDARD_LOGGER_NAME)

class Interval(NamedTuple):
    lb: int
    ub: int

StructDict = NewType('StructDict', dict[str, dict[str, Type]])

def postorder(a: AST, func: Callable[[AST], Any]) -> None:
    """Performs a postorder traversal of a, calling func on each node."""
    c: AST
    for c in a.get_children():
        postorder(c, func)
    func(a)


def preorder(a: AST, func: Callable[[AST], Any]) -> None:
    """Performs a preorder traversal of a, calling func on each node. func must not alter the children of its argument node"""
    c: AST
    func(a)
    for c in a.get_children():
        preorder(c, func)


def traverse(a: AST, pre: Callable[[AST], Any], post: Callable[[AST], Any]) -> None:
    c: AST
    pre(a)
    for c in a.get_children():
        traverse(c, pre, post)
    post(a)


def rename(v: AST, repl: AST, expr: AST) -> AST:
    # Special case: when expr is v
    if expr == v:
        return repl

    new: AST = deepcopy(expr)

    def rename_util(a: AST) -> None:
        if v == a:
            a.replace(repl)

    postorder(new, rename_util)
    return new


class AST():

    def __init__(self, ln: int, c: list[AST]) -> None:
        self.ln: int = ln
        self.tlid: int = -1
        self.bzid: int = -1
        self.atid: int = -1
        self.num_bz_parents: int = 0
        self.num_tl_parents: int = 0
        self.scq_size: int = 0
        self.name: str = ''
        self.bpd: int = 0
        self.wpd: int = 0
        self.formula_type = FormulaType.PROP
        self.type: Type = NOTYPE()
        self.is_ft: bool = True

        self._children: list[AST] = []
        self._parents: list[AST] = []

        child: AST
        for child in c:
            self._children.append(child)
            child._parents.append(self)
            if isinstance(self, TLExpr):
                child.num_tl_parents += 1
            elif isinstance(self, BZExpr):
                child.num_bz_parents += 1

    def get_children(self) -> list[AST]:
        return self._children

    def get_parents(self) -> list[AST]:
        return self._parents

    def num_children(self) -> int:
        return len(self._children)

    def num_parents(self) -> int:
        return len(self._parents)

    def get_child(self, i: int) -> AST:
        return self._children[i]

    def get_parent(self, i: int) -> AST:
        return self._parents[i]

    def tlid_name(self) -> str:
        return 'n'+str(self.tlid)

    def replace(self, new: AST) -> None:
        # Special case: if trying to replace this with itself
        if id(self) == id(new):
            return

        for p in self.get_parents():
            for i in range(0, len(p._children)):
                if p._children[i] == self:
                    p._children[i] = new

            new._parents.append(p)

            if isinstance(p, TLExpr):
                new.num_tl_parents += 1
            elif isinstance(p, BZExpr):
                new.num_bz_parents += 1

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

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self.get_children()]
        new = type(self)(self.ln, children)
        self.copy_attrs(new)
        return new


class TLExpr(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)

    def asm(self) -> str:
        return 'TL: n' + str(self.tlid) + ': '


class BZExpr(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.register: int = -1

    def asm(self) -> str:
        return 'BZ: '


class Literal(AST):

    def __init__(self, ln: int, a: list[AST]) -> None:
        super().__init__(ln,[])


class Constant(Literal):

    def __init__(self, ln: int, a: list[AST]) -> None:
        super().__init__(ln,[])
        self.value = 0

    def get_value(self) -> int|float:
        return self.value


class Integer(Constant, BZExpr):

    def __init__(self, ln: int, v: int) -> None:
        super().__init__(ln,[])
        self.val: int = v
        self.name = str(v)

        bit_length: int = v.bit_length()
        if v < 0:
            if bit_length <= 8:
                self.type = INT8()
            elif bit_length <= 16:
                self.type = INT16()
            elif bit_length <= 32:
                self.type = INT32()
            elif bit_length <= 64:
                self.type = INT64()
            else:
                logger.error(
                    f'{ln}: INTeger constant \'{v}\' not representable within 64 bits')
        else:
            if bit_length <= 8:
                self.type = UINT8()
            elif bit_length <= 16:
                self.type = UINT16()
            elif bit_length <= 32:
                self.type = UINT32()
            elif bit_length <= 64:
                self.type = UINT64()
            else:
                logger.error(
                    f'{ln}: Integer constant \'{v}\' not representable within 64 bits')

    def get_value(self) -> int:
        return self.value

    def __deepcopy__(self, memo):
        new = type(self)(self.ln, self.val)
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'iconst ' + str(self.name) + ''


class Float(Constant, BZExpr):

    def __init__(self, ln: int, v: float) -> None:
        super().__init__(ln,[])
        self.type = FLOAT()
        self.val: float = v
        self.name = str(v)

    def get_value(self) -> float:
        return self.value

    def asm(self) -> str:
        return super().asm() + 'fconst ' + str(self.name) + ''


class Variable(AST):

    def __init__(self, ln: int, n: str) -> None:
        super().__init__(ln,[])
        self.name: str = n
        self.reg: int = -1

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Variable) and __o.name == self.name


class Signal(Literal):

    def __init__(self, ln: int, n: str, t: Type) -> None:
        super().__init__(ln,[])
        self.name: str = n
        self.type: Type = t
        self.sid = -1


class Bool(Constant, BZExpr, TLExpr):

    def __init__(self, ln: int, v: bool) -> None:
        super().__init__(ln,[])
        self.type = BOOL()
        self.bpd: int = 0
        self.wpd: int = 0
        self.val: bool = v
        self.name = str(v)

    def tlid_name(self) -> str:
        return self.name

    def asm(self) -> str:
        return 'iconst ' + ('0' if self.name == 'False' else '1')


class Set(AST):

    def __init__(self, ln: int, m: list[AST]) -> None:
        super().__init__(ln, m)
        m.sort(key=lambda x: str(x))
        self.max_size: int = len(m)
        self.dynamic_size = None

    def get_max_size(self) -> int:
        return self.max_size

    def get_dynamic_size(self) -> AST | None:
        return self.dynamic_size

    def set_dynamic_size(self, s: AST) -> None:
        self.dynamic_size = s

    def __str__(self) -> str:
        s: str = '{'
        for m in self.get_children():
            s += str(m) + ','
        s = s[:-1] + '}'
        return s

    def asm(self) -> str:
        return super().asm() + 'set ' + str(self.name) + ''


class Struct(AST):

    def __init__(self, ln: int, n: str, m: dict[str, AST]) -> None:
        super().__init__(ln, [mem for mem in m.values()])
        self.type: Type = STRUCT(n)
        self.name: str = n
        self.members: dict[str, AST] = m

    def get_members(self) -> dict[str, AST]:
        return self.members

    def __deepcopy__(self, memo):
        members = deepcopy(self.members, memo)
        new = Struct(self.ln, self.name, members)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s: str = ''
        s += self.name + '('
        for i, e in self.members.items():
            s += i + '=' + str(e) + ','
        s = s[:-1] + ')'
        return s


class StructAccess(AST):

    def __init__(self, ln: int, s: AST, m: str) -> None:
        super().__init__(ln, [s])
        self.member: str = m

    def get_struct(self) -> Struct:
        return cast(Struct, self.get_child(0))

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.member)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return str(self.get_struct()) + '.' + self.member


class Operator(AST):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.arity: int = len(c)


class UnaryOperator(Operator):

    def __init__(self, ln: int, o: list[AST]) -> None:
        super().__init__(ln, o)
        assert len(o) == 1

    def get_operand(self) -> AST:
        return self.get_child(0)

    def __str__(self) -> str:
        return f'{self.name}({self.get_operand()})'


class BinaryOperator(Operator):

    def __init__(self, ln: int, l: list[AST]) -> None:
        super().__init__(ln, l)
        assert len(l) == 2

    def get_lhs(self) -> AST:
        return self.get_child(0)

    def get_rhs(self) -> AST:
        return self.get_child(1)

    def __str__(self) -> str:
        return f'({self.get_lhs()}){self.name}({self.get_rhs()})'


# only used for assembly generation
class Duplicate(UnaryOperator, BZExpr):

    def __init__(self, ln: int, d: AST) -> None:
        super().__init__(ln, [d])

    def get_dup(self) -> AST:
        return self.get_operand()

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = Duplicate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'dup'


# only used for assembly generation
class TLAtomicLoad(UnaryOperator, TLExpr):

    def __init__(self, ln: int, l: BZExpr) -> None:
        super().__init__(ln, [l])
        self.tlid = l.tlid

    def get_load(self) -> BZExpr:
        return cast(BZExpr, self.get_operand())

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = TLAtomicLoad(self.ln, cast(BZExpr, children[0]))
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'load a' + str(self.get_load().atid)


# only used for assembly generation
class TLSignalLoad(UnaryOperator, TLExpr):

    def __init__(self, ln: int, l: Signal) -> None:
        super().__init__(ln, [l])
        self.tlid = l.tlid

    def get_load(self) -> Signal:
        return cast(Signal, self.get_operand())

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = TLSignalLoad(self.ln, cast(Signal, children[0]))
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'load s' + str(self.get_load().sid)


# only used for assembly generation
class BZAtomicLoad(UnaryOperator, BZExpr):

    def __init__(self, ln: int, l: TLExpr) -> None:
        super().__init__(ln, [l])
        self.tlid = l.tlid

    def get_load(self) -> TLExpr:
        return cast(TLExpr, self.get_operand())

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BZAtomicLoad(self.ln, cast(TLExpr, children[0]))
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        load = self.get_load()
        return super().asm() + f'aload {str(load.atid)}'


# only used for assembly generation
class BZSignalLoad(UnaryOperator, BZExpr):

    def __init__(self, ln: int, l: Signal) -> None:
        super().__init__(ln, [l])
        self.tlid = l.tlid

    def get_load(self) -> Signal:
        return cast(Signal, self.get_operand())

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BZSignalLoad(self.ln, cast(Signal, children[0]))
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        load = self.get_load()
        return super().asm() + f'sload {str(load.sid)}'


# only used for assembly generation
class BZAtomicStore(UnaryOperator, BZExpr):

    def __init__(self, ln: int, s: BZExpr) -> None:
        super().__init__(ln, [s])

    def get_store(self) -> BZExpr:
        return cast(BZExpr, self.get_operand())

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BZAtomicStore(self.ln, cast(BZExpr, children[0]))
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + f'astore {self.get_store().atid}'


# only used for assembly generation
class RegisterStore(UnaryOperator, BZExpr):

    def __init__(self, ln: int, s: BZExpr, r: int) -> None:
        super().__init__(ln, [s])
        self.register: int = r
        s.register = r

    def get_store(self) -> BZExpr:
        return cast(BZExpr, self.get_operand())

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = RegisterStore(self.ln, cast(BZExpr, children[0]), self.register)
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + f'rstore {self.register}'


# only used for assembly generation
class RegisterLoad(UnaryOperator, BZExpr):

    def __init__(self, ln: int, l: BZExpr) -> None:
        super().__init__(ln, [l])
        self.register: int = l.register

    def get_load(self) -> BZExpr:
        return cast(BZExpr, self.get_operand())

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = RegisterLoad(self.ln, cast(BZExpr, children[0]))
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + f'rload {self.register}'


class Function(Operator):

    def __init__(self, ln: int, n: str, r: Type, a: list[AST]) -> None:
        super().__init__(ln, a)
        self.name: str = n
        self.type: Type = r


class SetAggOperator(Operator):

    def __init__(self, ln: int, s: Set, v: Variable,  e: AST) -> None:
        super().__init__(ln, [s, v, e])

    def get_set(self) -> Set:
        return cast(Set, self.get_child(0))

    def get_boundvar(self) -> Variable:
        return cast(Variable, self.get_child(1))

    def get_expr(self) -> AST:
        return self.get_child(2)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, cast(Set, children[0]), cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return self.name + '(' + str(self.get_boundvar()) + ':' + \
            str(self.get_set()) + ')' + '(' + str(self.get_expr()) + ')'


class ForEach(SetAggOperator):

    def __init__(self, ln: int, s: Set, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'foreach'


class ForSome(SetAggOperator):

    def __init__(self, ln: int, s: Set, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'forsome'


class ForExactlyN(SetAggOperator):

    def __init__(self, ln: int, s: Set, n: AST, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'forexactlyn'
        self.num: AST = n
        self._children.append(self.num)

    def get_num(self) -> AST:
        return self.num

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ForExactlyN(self.ln, cast(Set, children[0]), children[3], cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class ForAtLeastN(SetAggOperator):

    def __init__(self, ln: int, s: Set, n: AST, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'foratleastn'
        self.num: AST = n
        self._children.append(self.num)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ForExactlyN(self.ln, cast(Set, children[0]), children[3], cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class ForAtMostN(SetAggOperator):

    def __init__(self, ln: int, s: Set, n: AST, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = 'foratmostn'
        self.num: AST = n
        self._children.append(self.num)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ForExactlyN(self.ln, cast(Set, children[0]), children[3], cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class Count(BZExpr):

    def __init__(self, ln: int, n: AST, c: list[AST]) -> None:
        # Note: all members of c must be of type Boolean
        super().__init__(ln, c)
        self.num: AST = n
        self.type = UINT8() # TODO: set this more precisely

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        if len(children) > 1:
            new = Count(self.ln, children[0], children[1:])
        else:
            new = Count(self.ln, children[0], [])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s = 'count('
        for c in self.get_children():
            s += str(c) + ','
        return s[:-1] + ')'

    def asm(self) -> str:
        return super().asm() + f'count {self.num}'


class BitwiseOperator(Operator):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)


class BitwiseAnd(BitwiseOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '&'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseAnd(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'and'


class BitwiseOr(BitwiseOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '|'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseOr(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'or'


class BitwiseXor(BitwiseOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '^'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'xor'


class BitwiseShiftLeft(BitwiseOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '<<'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseShiftLeft(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'lshift'


class BitwiseShiftRight(BitwiseOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '>>'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseShiftRight(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'rshift'


class BitwiseNegate(BitwiseOperator, UnaryOperator):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, [o])
        self.name: str = '~'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'bwneg'


class ArithmeticOperator(BZExpr):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)


class ArithmeticAdd(ArithmeticOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '+'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticAdd(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == FLOAT() else 'i') + 'add'


class ArithmeticSubtract(ArithmeticOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '-'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticSubtract(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == FLOAT() else 'i') + 'sub'


class ArithmeticMultiply(ArithmeticOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '+'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticMultiply(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == FLOAT() else 'i') + 'mul'


class ArithmeticDivide(ArithmeticOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '/'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticDivide(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == FLOAT() else 'i') + 'div'


class ArithmeticModulo(ArithmeticOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '%'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticModulo(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'mod'


class ArithmeticNegate(ArithmeticOperator, UnaryOperator):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, [o])
        self.name: str = '-'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + ('f' if self.type == FLOAT() else 'i') + 'neg'


class RelationalOperator(BZExpr, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class Equal(RelationalOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '=='

    def asm(self) -> str:
        return super().asm() + 'eq'


class NotEqual(RelationalOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '!='

    def asm(self) -> str:
        return super().asm() + 'neq'


class GreaterThan(RelationalOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>'

    def asm(self) -> str:
        return super().asm() + ('i' if is_integer_type(self.get_lhs().type) else 'f') + 'gt'


class LessThan(RelationalOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<'

    def asm(self) -> str:
        return super().asm() + ('i' if is_integer_type(self.get_lhs().type) else 'f') + 'lt'


class GreaterThanOrEqual(RelationalOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '>='

    def asm(self) -> str:
        return super().asm() + ('i' if is_integer_type(self.get_lhs().type) else 'f') + 'gte'


class LessThanOrEqual(RelationalOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = '<='

    def asm(self) -> str:
        return super().asm() + ('i' if is_integer_type(self.get_lhs().type) else 'f') + 'lte'


class LogicalOperator(TLExpr):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.bpd = min([child.bpd for child in c])
        self.wpd = max([child.wpd for child in c])


class LogicalOr(LogicalOperator):

    def __init__(self, ln: int, c: list[AST]) -> None:
        assert len(c) > 1
        super().__init__(ln, c)
        self.name: str = '||'

    def __str__(self) -> str:
        s: str = ''
        for arg in self.get_children():
            s += str(arg) + '||'
        return s[:-2]

    def asm(self) -> str:
        s: str = super().asm() + 'or'
        for c in self.get_children():
            s += ' ' + c.tlid_name()
        return s + ''


class LogicalAnd(LogicalOperator):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.name: str = '&&'

    def __str__(self) -> str:
        s: str = ''
        for arg in self.get_children():
            s += str(arg) + '&&'
        return s[:-2]

    def asm(self) -> str:
        s: str = super().asm() + 'and'
        for c in self.get_children():
            s += ' ' + c.tlid_name()
        return s + ''


class LogicalXor(LogicalOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '^^'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'xor ' + self.get_lhs().tlid_name() + ' ' + self.get_rhs().tlid_name()


class LogicalImplies(LogicalOperator, BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = '->'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalImplies(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'impl ' + self.get_lhs().tlid_name() + ' ' + self.get_rhs().tlid_name()


class LogicalNegate(LogicalOperator, UnaryOperator):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln, [o])
        self.name: str = '!'

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return super().asm() + 'not ' + self.get_operand().tlid_name()


class TemporalOperator(TLExpr):

    def __init__(self, ln: int, c: list[AST], l: int, u: int) -> None:
        super().__init__(ln, c)
        self.interval = Interval(lb=l,ub=u)


class FutureTimeOperator(TemporalOperator):

    def __init__(self, ln: int, c: list[AST], l: int, u: int) -> None:
        super().__init__(ln, c, l, u)


class PastTimeOperator(TemporalOperator):

    def __init__(self, ln: int, c: list[AST], l: int, u: int) -> None:
        super().__init__(ln, c, l, u)


# cannot inherit from BinaryOperator due to multiple inheriting classes
# with different __init__ signatures
class FutureTimeBinaryOperator(TemporalOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, [lhs, rhs], l, u)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def get_lhs(self) -> AST:
        return self.get_child(0)

    def get_rhs(self) -> AST:
        return self.get_child(1)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.get_lhs()!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})'


class Until(FutureTimeBinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'U'

    def asm(self) -> str:
        return super().asm() + 'until ' + self.get_lhs().tlid_name() + ' ' + self.get_rhs().tlid_name() + ' ' + \
            str(self.interval.lb) + ' ' + str(self.interval.ub)


class Release(FutureTimeBinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'R'

    def asm(self) -> str:
        return super().asm() + 'release ' + self.get_lhs().tlid_name() + ' ' + self.get_rhs().tlid_name() + ' ' + \
            str(self.interval.lb) + ' ' + str(self.interval.ub)


class FutureTimeUnaryOperator(FutureTimeOperator):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def get_operand(self) -> AST:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})'


class Global(FutureTimeUnaryOperator):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'G'

    def asm(self) -> str:
        return super().asm() + 'global ' + self.get_operand().tlid_name() + ' ' + \
            str(self.interval.lb) + ' ' + str(self.interval.ub)


class Future(FutureTimeUnaryOperator):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'F'

    def asm(self) -> str:
        return super().asm() + 'future ' + self.get_operand().tlid_name() + ' ' + \
            str(self.interval.lb) + ' ' + str(self.interval.ub)


class PastTimeBinaryOperator(PastTimeOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, [lhs, rhs], l, u)

    def get_lhs(self) -> AST:
        return self.get_child(0)

    def get_rhs(self) -> AST:
        return self.get_child(1)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'({self.get_lhs()!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})'


class Since(PastTimeBinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = 'S'

    def asm(self) -> str:
        return super().asm() + 'since ' + self.get_lhs().tlid_name() + ' ' + self.get_rhs().tlid_name() + ' ' + \
            str(self.interval.lb) + ' ' + str(self.interval.ub)


class PastTimeUnaryOperator(PastTimeOperator):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, [o], l, u)

    def get_operand(self) -> AST:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f'{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})'


class Historical(PastTimeUnaryOperator):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'H'

    def asm(self) -> str:
        return super().asm() + 'his ' + self.get_operand().tlid_name() + ' ' + \
            str(self.interval.lb) + ' ' + str(self.interval.ub)


class Once(PastTimeUnaryOperator):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = 'O'

    def asm(self) -> str:
        return super().asm() + 'once ' + self.get_operand().tlid_name() + ' ' + \
            str(self.interval.lb) + ' ' + str(self.interval.ub)

class Specification(TLExpr):

    def __init__(self, ln: int, lbl: str, f: int, e: AST) -> None:
        super().__init__(ln, [e])
        self.name: str = lbl
        self.formula_number: int = f

    def get_expr(self) -> AST:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = Specification(self.ln, self.name, self.formula_number, children[0])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return (str(self.formula_number) if self.name == '' else self.name) + ': ' + str(self.get_expr())

    def asm(self) -> str:
        top: AST = self.get_child(0)
        return super().asm() + 'end ' + top.tlid_name() + ' f' + str(self.formula_number) + ''


class Program(TLExpr):

    def __init__(self, ln: int, st: StructDict, s: list[Specification], c: dict[int, Specification]) -> None:
        super().__init__(ln, [cast(AST,spec) for spec in s])
        self.structs = st
        self.specs = s
        self.contracts = c
        self.is_type_correct = False
        self.is_boolean_normal_form = False
        self.is_negative_normal_form = False
        self.is_set_agg_free = False
        self.is_struct_access_free = False
        self.is_cse_reduced = False

    def __str__(self) -> str:
        ret: str = ''
        s: AST
        for s in self.get_children():
            ret += str(s) + '\n'
        return ret[:-1]

    def asm(self) -> str:
        return super().asm() + 'endsequence'
