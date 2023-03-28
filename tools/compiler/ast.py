from __future__ import annotations
from cmath import atan
from copy import deepcopy
import inspect
# import inspect
import sys
from typing import Any, Callable, NamedTuple, NewType, cast
from logging import getLogger

from simplejson import load

from .logger import *
from .type import *

logger = getLogger(COLOR_LOGGER_NAME)

class Interval(NamedTuple):
    lb: int
    ub: int

StructDict = NewType("StructDict", dict[str, dict[str, Type]])


def postorder(a: AST, func: Callable[[AST], Any]) -> None:
    """Performs a postorder traversal of a, calling func on each node."""
    c: AST
    for c in a.get_children():
        postorder(c, func)
    func(a)


def postorder_iter(a: AST, func: Callable[[AST], Any]) -> None:
    ast_stack: list[AST] = []
    int_stack: list[int] = []
    cur_ast: AST|None = a
    cur_int: int = 0
    
    while not len(ast_stack) == 0 or cur_ast != None:
        if cur_ast != None:
            ast_stack.append(cur_ast)
            int_stack.append(cur_int+1)
            cur_ast = None if cur_int >= len(cur_ast.get_children()) else cur_ast.get_child(cur_int)
        else:
            peek_ast: AST = ast_stack[len(ast_stack)-1]
            peek_int: int = int_stack[len(int_stack)-1]
            if peek_int < len(peek_ast.get_children()):
                int_stack[len(int_stack)-1] += 1
                cur_ast = peek_ast.get_child(peek_int)
                cur_int = 0
            else:
                func(peek_ast)
                ast_stack.pop()
                int_stack.pop()


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
    is_instruction: bool = False

    def __init__(self, ln: int, c: list[AST]) -> None:
        self.ln: int = ln
        self.tlid: int = -1
        self.atid: int = -1
        self.total_scq_size: int = 0
        self.scq_size: int = 0
        self.name: str = ""
        self.bpd: int = 0
        self.wpd: int = 0
        self.formula_type = FormulaType.PROP
        self.type: Type = NOTYPE()

        self._children: list[AST] = []
        self._parents: list[AST] = []

        child: AST
        for child in c:
            self._children.append(child)
            child._parents.append(self)

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

    def add_child(self, c: AST) -> None:
        self._children.append(c)

    def remove_child(self, c: AST) -> None:
        self._children.remove(c)

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

        new.formula_type = self.formula_type

    def __str__(self) -> str:
        return self.name

    def copy_attrs(self, new: AST) -> None:
        new.tlid = self.tlid
        new.atid = self.atid
        new.scq_size = self.scq_size
        new.name = self.name
        new.bpd = self.bpd
        new.wpd = self.wpd
        new.formula_type = self.formula_type
        new.type = self.type

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self.get_children()]
        new = type(self)(self.ln, children)
        self.copy_attrs(new)
        return new


class Instruction(AST):
    """Abstract base class for module-specific instructions"""

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)

    def asm(self) -> str:
        logger.error(f"Invalid instruction (class should inherit from TLInstruction or BZInstruction, not Instruction)")
        return "ERROR"


class TLInstruction(Instruction):
    """Abstract base class for AST nodes that have valid TL assembly instructions"""

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.scq_size = 1

    def asm(self) -> str:
        return f"n{self.tlid}"


class BZInstruction(Instruction):
    """Abstract base class for AST nodes that have valid BZ assembly instructions"""

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)

    def asm(self) -> str:
        return ""


class ATInstruction(Instruction):
    """Class for AST nodes that have valid AT assembly instructions"""

    def __init__(self, ln: int, n: str, f: str, a: list[AST], r: RelationalOperator, c: AST) -> None:
        super().__init__(ln, []) 
        self.name: str = n
        self.filter: str = f
        self.args: list[AST] = a
        self.rel_op: RelationalOperator = r
        self.compare: AST = c

    def __str__(self) -> str:
        s: str = f"{self.filter}("
        for arg in self.args:
            s += f"{arg.name},"
        s = s[:-1] + ") "
        s += f"{self.rel_op.name} {self.compare.name}"
        return s

    # def __deepcopy__(self, memo):
    #     new = ATInstruction(
    #         self.ln, 
    #         self.filter, 
    #         deepcopy(self.relop, memo), 
    #         deepcopy(self.get_compare(), memo), 
    #         deepcopy(self.get_filter_args(), memo)
    #     )
    #     self.copy_attrs(new)
    #     return new

    def asm(self) -> str:
        s: str = f"a{self.atid} {self.filter}("
        for arg in self.args:
            s += f"s{arg.sid}," if isinstance(arg, Signal) else f"{arg.name},"
        s = s[:-1] + ") "
        s += f"{self.rel_op.name} "
        s += f"s{self.compare.sid} " if isinstance(self.compare, Signal) else f"{self.compare.name}"
        return s


class Literal(AST):

    def __init__(self, ln: int, a: list[AST]) -> None:
        super().__init__(ln,[])


class Constant(Literal):

    def __init__(self, ln: int, a: list[AST]) -> None:
        super().__init__(ln,[])
        self.value = 0

    def get_value(self) -> int|float:
        return self.value


class Integer(Constant):

    def __init__(self, ln: int, v: int) -> None:
        super().__init__(ln,[])
        self.value: int = v
        self.name = str(v)
        self.type = INT()

        if v.bit_length() > INT.width:
            logger.error(f"{ln} Constant \"{v}\" not representable in configured int width (\"{INT.width}\").")

    def get_value(self) -> int:
        return self.value

    def __deepcopy__(self, memo):
        new = Integer(self.ln, self.value)
        self.copy_attrs(new)
        return new


class Float(Constant):

    def __init__(self, ln: int, v: float) -> None:
        super().__init__(ln,[])
        self.type = FLOAT()
        self.value: float = v
        self.name = str(v)

        # TODO: Fix this
        # if len(v.hex()[2:]) > FLOAT.width:
        #     logger.error(f"{ln} Constant \"{v}\" not representable in configured float width (\"{FLOAT.width}\").")

    def get_value(self) -> float:
        return self.value

    def __deepcopy__(self, memo):
        new = Float(self.ln, self.value)
        self.copy_attrs(new)
        return new


class Variable(AST):
    """AST node representing a bound variable in set aggregation expressions"""

    def __init__(self, ln: int, n: str) -> None:
        super().__init__(ln,[])
        self.name: str = n

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Variable) and __o.name == self.name


class Signal(Literal, BZInstruction):

    def __init__(self, ln: int, n: str, t: Type) -> None:
        super().__init__(ln,[])
        self.name: str = n
        self.type: Type = t
        self.sid = -1

    def __deepcopy__(self, memo):
        copy = Signal(self.ln, self.name, self.type)
        copy.sid = self.sid
        return copy

    def asm(self) -> str:
        return f"load s{self.sid}"


class Atomic(Literal, TLInstruction):

    def __init__(self, ln: int, n: str) -> None:
        super().__init__(ln, [])
        self.name: str = n
        self.type: Type = BOOL()

    def __deepcopy__(self, memo):
        copy = Atomic(self.ln, self.name)
        self.copy_attrs(copy)
        return copy

    def asm(self) -> str:
        return f"{super().asm()} load a{self.atid}" 


class Bool(Constant):

    def __init__(self, ln: int, v: bool) -> None:
        super().__init__(ln,[])
        self.type = BOOL()
        self.bpd: int = 0
        self.wpd: int = 0
        self.value: bool = v
        self.name = str(v)

    def tlid_name(self) -> str:
        return self.name

    # def asm(self) -> str:
    #     return "iconst " + ("0" if self.name == "False" else "1")


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
        s: str = "{"
        for m in self.get_children():
            s += str(m) + ","
        s = s[:-1] + "}"
        return s


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
        s: str = ""
        s += self.name + "("
        for i, e in self.members.items():
            s += i + "=" + str(e) + ","
        s = s[:-1] + ")"
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
        return str(self.get_struct()) + "." + self.member


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
        return f"{self.name}({self.get_operand()})"


class BinaryOperator(Operator):

    def __init__(self, ln: int, l: list[AST]) -> None:
        super().__init__(ln, l)
        assert len(l) == 2

    def get_lhs(self) -> AST:
        return self.get_child(0)

    def get_rhs(self) -> AST:
        return self.get_child(1)

    def __str__(self) -> str:
        return f"({self.get_lhs()}){self.name}({self.get_rhs()})"


# only used for assembly generation
class Duplicate(UnaryOperator, BZInstruction):

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
        return f"dup"


# only used for assembly generation
class TLAtomicLoad(TLInstruction):

    def __init__(self, ln: int, l: BZAtomicStore) -> None:
        super().__init__(ln, [l])

    def get_load(self) -> BZAtomicStore:
        return cast(BZAtomicStore, self.get_child(0))

    def __str__(self) -> str:
        return f"TLLoad({self.get_load()})"

    def asm(self) -> str:
        return f"{super().asm()} load a{self.get_load().atid}"


# only used for assembly generation
class BZAtomicLoad(BZInstruction):

    def __init__(self, ln: int, l: TLInstruction) -> None:
        super().__init__(ln, [l])

    def get_load(self) -> BZAtomicLoad:
        return cast(BZAtomicLoad, self.get_child(0))

    def asm(self) -> str:
        return f"aload {self.atid}"


# only used for assembly generation
class BZAtomicStore(BZInstruction):

    def __init__(self, ln: int, s: BZInstruction) -> None:
        super().__init__(ln, [s])

    def get_store(self) -> BZInstruction:
        return cast(BZInstruction, self.get_child(0))

    def __str__(self) -> str:
        return f"BZStore({self.get_store()})"

    def asm(self) -> str:
        return f"astore {self.atid}"


class Function(Operator):

    def __init__(self, ln: int, n: str, a: list[AST]) -> None:
        super().__init__(ln, a)
        self.name: str = n

    def __deepcopy__(self, memo):
        return Function(self.ln, self.name, deepcopy(self.get_children(), memo))



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
        return self.name + "(" + str(self.get_boundvar()) + ":" + \
            str(self.get_set()) + ")" + "(" + str(self.get_expr()) + ")"


class ForEach(SetAggOperator):

    def __init__(self, ln: int, s: Set, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = "foreach"


class ForSome(SetAggOperator):

    def __init__(self, ln: int, s: Set, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = "forsome"


class ForExactlyN(SetAggOperator):

    def __init__(self, ln: int, s: Set, n: AST, v: Variable, e: AST) -> None:
        super().__init__(ln, s, v, e)
        self.name: str = "forexactlyn"
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
        self.name: str = "foratleastn"
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
        self.name: str = "foratmostn"
        self.num: AST = n
        self._children.append(self.num)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ForExactlyN(self.ln, cast(Set, children[0]), children[3], cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class Count(BZInstruction):

    def __init__(self, ln: int, n: AST, c: list[AST]) -> None:
        # Note: all members of c must be of type Boolean
        super().__init__(ln, c)
        self.num: AST = n
        self.type = INT()

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        if len(children) > 1:
            new = Count(self.ln, children[0], children[1:])
        else:
            new = Count(self.ln, children[0], [])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s = "count("
        for c in self.get_children():
            s += str(c) + ","
        return s[:-1] + ")"

    def asm(self) -> str:
        return f"count {self.num}"


class BitwiseOperator(Operator):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)


class BitwiseAnd(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "&"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseAnd(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return "and"


class BitwiseOr(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "|"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseOr(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return "or"


class BitwiseXor(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "^"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return "xor"


class BitwiseShiftLeft(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "<<"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseShiftLeft(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return "lshift"


class BitwiseShiftRight(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = ">>"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseShiftRight(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return "rshift"


class BitwiseNegate(BitwiseOperator, UnaryOperator, BZInstruction):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, [o])
        self.name: str = "~"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return "bwneg"


class ArithmeticOperator(Operator):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)


class ArithmeticAdd(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "+"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticAdd(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return ("f" if self.type == FLOAT() else "i") + "add"


class ArithmeticSubtract(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "-"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticSubtract(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return ("f" if self.type == FLOAT() else "i") + "sub"


class ArithmeticMultiply(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "+"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticMultiply(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return ("f" if self.type == FLOAT() else "i") + "mul"


class ArithmeticDivide(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "/"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticDivide(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return ("f" if self.type == FLOAT() else "i") + "div"


class ArithmeticModulo(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "%"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticModulo(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return "mod"


class ArithmeticNegate(ArithmeticOperator, UnaryOperator, BZInstruction):

    def __init__(self, ln: int, o: AST) -> None:
        super().__init__(ln, [o])
        self.name: str = "-"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return ("f" if self.type == FLOAT() else "i") + "neg"


class RelationalOperator(BinaryOperator):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name = ""

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class Equal(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = "=="

    def asm(self) -> str:
        return "eq"


class NotEqual(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = "!="

    def asm(self) -> str:
        return "neq"


class GreaterThan(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = ">"

    def asm(self) -> str:
        return ("i" if is_integer_type(self.get_lhs().type) else "f") + "gt"


class LessThan(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = "<"

    def asm(self) -> str:
        return ("i" if is_integer_type(self.get_lhs().type) else "f") + "lt"


class GreaterThanOrEqual(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = ">="

    def asm(self) -> str:
        return ("i" if is_integer_type(self.get_lhs().type) else "f") + "gte"


class LessThanOrEqual(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, lhs, rhs)
        self.name: str = "<="

    def asm(self) -> str:
        return ("i" if is_integer_type(self.get_lhs().type) else "f") + "lte"


class LogicalOperator(Operator):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.bpd = min([child.bpd for child in c])
        self.wpd = max([child.wpd for child in c])


class LogicalOr(LogicalOperator, TLInstruction):

    def __init__(self, ln: int, c: list[AST]) -> None:
        assert len(c) > 1
        super().__init__(ln, c)
        self.name: str = "||"

    def __str__(self) -> str:
        s: str = ""
        for arg in self.get_children():
            s += str(arg) + "||"
        return s[:-2]

    def asm(self, ) -> str:
        s: str = f"{super().asm()} or"
        for c in self.get_children():
            s += f" {c.tlid_name()}"
        return s


class LogicalAnd(LogicalOperator, TLInstruction):

    def __init__(self, ln: int, c: list[AST]) -> None:
        super().__init__(ln, c)
        self.name: str = "&&"

    def __str__(self) -> str:
        s: str = ""
        for arg in self.get_children():
            s += str(arg) + "&&"
        return s[:-2]

    def asm(self, ) -> str:
        s: str = f"{super().asm()} and"
        for c in self.get_children():
            s += f" {c.tlid_name()}"
        return s


class LogicalXor(LogicalOperator, BinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "^^"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return f"{super().asm()} xor {self.get_lhs().tlid_name()} {self.get_rhs().tlid_name()}"


class LogicalImplies(LogicalOperator, BinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST) -> None:
        super().__init__(ln, [lhs, rhs])
        self.name: str = "->"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalImplies(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return f"{super().asm()} impl {self.get_lhs().tlid_name()} {self.get_rhs().tlid_name()}"


class LogicalNegate(LogicalOperator, UnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: AST):
        super().__init__(ln, [o])
        self.name: str = "!"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def asm(self) -> str:
        return f"{super().asm()} not {self.get_operand().tlid_name()}" 


class TemporalOperator(Operator):

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
        return f"({self.get_lhs()!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"


class Until(FutureTimeBinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = "U"

    def asm(self) -> str:
        return f"{super().asm()} until {self.get_lhs().tlid_name()} {self.get_rhs().tlid_name()} {self.interval.lb} {self.interval.ub}"


class Release(FutureTimeBinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = "R"

    def asm(self) -> str:
        return f"{super().asm()} release {self.get_lhs().tlid_name()} {self.get_rhs().tlid_name()} {self.interval.lb} {self.interval.ub}"


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
        return f"{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"


class Global(FutureTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = "G"

    def asm(self) -> str:
        return f"{super().asm()} global {self.get_operand().tlid_name()} {self.interval.lb} {self.interval.ub}"


class Future(FutureTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = "F"

    def asm(self) -> str:
        return f"{super().asm()} future {self.get_operand().tlid_name()} {self.interval.lb} {self.interval.ub}"


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
        return f"({self.get_lhs()!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"


class Since(PastTimeBinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: AST, rhs: AST, l: int, u: int) -> None:
        super().__init__(ln, lhs, rhs, l, u)
        self.name: str = "S"

    def asm(self) -> str:
        return f"{super().asm()} since {self.get_lhs().tlid_name()} {self.get_rhs().tlid_name()} {self.interval.lb} {self.interval.ub}"


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
        return f"{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"


class Historical(PastTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = "H"

    def asm(self) -> str:
        return f"{super().asm()} his {self.get_operand().tlid_name()} {self.interval.lb} {self.interval.ub}"


class Once(PastTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: AST, l: int, u: int) -> None:
        super().__init__(ln, o, l, u)
        self.name: str = "O"

    def asm(self) -> str:
        return f"{super().asm()} once {self.get_operand().tlid_name()} {self.interval.lb} {self.interval.ub}"


class Specification(TLInstruction):

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
        return (str(self.formula_number) if self.name == "" else self.name) + ": " + str(self.get_expr())

    def asm(self) -> str:
        return f"{super().asm()} end n{self.get_expr().tlid} f{self.formula_number}"


class Contract(AST):

    def __init__(self, ln: int, lbl: str, f1: int, f2: int, f3: int, a: TLInstruction, g: TLInstruction) -> None:
        super().__init__(ln, [a, g])
        self.name: str = lbl
        self.formula_numbers: tuple[int,int,int] = (f1,f2,f3)

    def get_assumption(self) -> TLInstruction:
        return cast(TLInstruction, self.get_child(0))

    def get_guarantee(self) -> TLInstruction:
        return cast(TLInstruction, self.get_child(1))

    def __str__(self) -> str:
        return f"({self.get_assumption()})=>({self.get_guarantee()})"


class SpecificationSet(TLInstruction):

    def __init__(self, ln: int, t: FormulaType, s: list[Specification|Contract]) -> None:
        super().__init__(ln, [cast(AST, spec) for spec in s])
        self.formula_type = t

    def asm(self) -> str:
        return f"{super().asm()} endsequence"


class Program(AST):

    def __init__(self, ln: int, st: StructDict, a: dict[str, AST], fts: SpecificationSet, pts: SpecificationSet) -> None:
        super().__init__(ln, [fts, pts])

        # Data
        self.timestamp_width: int = 0
        self.structs: StructDict = st
        self.atomics: dict[str, AST] = a
        self.ft_spec_set: SpecificationSet = fts
        self.pt_spec_set: SpecificationSet = pts
        self.assembly: list[Instruction] = []
        self.scq_assembly: list[tuple[int,int]] = []
        self.signal_mapping: dict[str,int] = {}
        self.contracts: dict[str,tuple[int,int,int]] = {}

        # Computable properties
        self.total_memory: int = -1
        self.cpu_wcet: int = -1
        self.fpga_wcet: float = -1

        # Predicates
        self.is_type_correct: bool = False
        self.is_set_agg_free: bool = False
        self.is_struct_access_free: bool = False
        self.is_cse_reduced: bool = False

    def get_ft_specs(self) -> SpecificationSet:
        return cast(SpecificationSet, self.get_child(0))

    def get_pt_specs(self) -> SpecificationSet:
        return cast(SpecificationSet, self.get_child(1))

    def __str__(self) -> str:
        ret: str = ""
        s: AST
        for s in self.get_children():
            ret += str(s) + "\n"
        return ret[:-1]

    def __deepcopy__(self, memo):
        return Program(
            self.ln, 
            deepcopy(self.structs, memo), 
            deepcopy(self.atomics, memo), 
            deepcopy(self.ft_spec_set, memo),
            deepcopy(self.pt_spec_set, memo)
        )
