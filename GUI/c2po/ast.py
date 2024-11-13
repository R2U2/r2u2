from __future__ import annotations
from copy import deepcopy
from typing import Any, Dict, Callable, NamedTuple, NewType, cast, List, Tuple
from logging import getLogger

from .type import R2U2Implementation

from .logger import *
from .type import *

logger = getLogger(STANDARD_LOGGER_NAME)

class Interval(NamedTuple):
    lb: int
    ub: int

StructDict = NewType("StructDict", Dict[str, List[Tuple[str, Type]]])


def postorder_recursive(node: Node, func: Callable[[Node], Any]):
    """Perform a postorder traversal of node, calling func on each node."""
    c: Node
    for c in node.get_children():
        postorder_recursive(c, func)
    func(node)


def postorder_iterative(node: Node, func: Callable[[Node], Any]):
    """Perform an iterative postorder traversal of node, calling func on each node."""
    stack: List[tuple[bool, Node]] = []
    visited: set[int] = set()

    stack.append((False, node))

    while len(stack) > 0:
        cur = stack.pop()

        if cur[0]:
            func(cur[1])
            continue
        elif id(cur[1]) in visited:
            continue

        visited.add(id(cur[1]))
        stack.append((True, cur[1]))
        for child in reversed(cur[1].get_children()):
            stack.append((False, child))


def preorder(node: Node, func: Callable[[Node], Any]):
    """Perform a preorder traversal of a, calling func on each node. func must not alter the children of its argument node."""
    c: Node
    func(node)
    for c in node.get_children():
        preorder(c, func)


def rename(v: Node, repl: Node, expr: Node) -> Node:
    """Traverse expr and replace each node equal to v with repl."""
    # Special case: when expr is v
    if expr == v:
        return repl

    new: Node = deepcopy(expr)

    def rename_util(a: Node):
        if v == a:
            a.replace(repl)

    postorder_recursive(new, rename_util)
    return new


class Node():
    is_instruction: bool = False

    def __init__(self, ln: int, c: List[Node]):
        self.ln: int = ln
        self.total_scq_size: int = 0
        self.scq_size: int = 0
        self.name: str = ""
        self.symbol: str = ""
        self.bpd: int = 0
        self.wpd: int = 0
        self.formula_type = FormulaType.PROP
        self.type: Type = NOTYPE()
        self.ftid: int = -1
        self.ptid: int = -1
        self.bzid: int = -1
        self.atid: int = -1

        self._children: List[Node] = []
        self._parents: List[Node] = []

        for child in c:
            self._children.append(child)
            child._parents.append(self)

    def get_children(self) -> List[Node]:
        return self._children

    def get_parents(self) -> List[Node]:
        return self._parents
        
    def has_tl_parent(self) -> bool:
        for p in self._parents:
            if isinstance(p, TLInstruction):
                return True
        return False

    def num_children(self) -> int:
        return len(self._children)

    def num_parents(self) -> int:
        return len(self._parents)

    def get_child(self, i: int) -> Node:
        return self._children[i]

    def get_parent(self, i: int) -> Node:
        return self._parents[i]

    def add_child(self, child: Node):
        self._children.append(child)
        child._parents.append(self)

    def remove_child(self, child: Node):
        self._children.remove(child)
        child._parents.remove(self)

    def replace(self, new: Node):
        """Replaces 'self' with 'new', setting the parents' children of 'self' to 'new'. Note that'self' is orphaned as a result."""

        # Special case: if trying to replace this with itself
        if id(self) == id(new):
            return

        for parent in self.get_parents():
            for i in range(0, len(parent._children)):
                if id(parent._children[i]) == id(self):
                    parent._children[i] = new

            new._parents.append(parent)

        for child in self.get_children():
            if self in child.get_parents():
                child.get_parents().remove(self)

        new.formula_type = self.formula_type

    def ft_asm(self) -> str:
        raise NotImplementedError

    def pt_asm(self) -> str:
        raise NotImplementedError

    def bz_asm(self) -> str:
        raise NotImplementedError

    def at_asm(self) -> str:
        raise NotImplementedError
    
    def ftid_str(self) -> str:
        raise NotImplementedError
    
    def ptid_str(self) -> str:
        raise NotImplementedError
    
    def bzid_str(self) -> str:
        raise NotImplementedError
    
    def atid_str(self) -> str:
        if self.atid < 0:
            logger.critical(f" Node '{self}' never assigned atid.")
            return ""
        return f"a{self.atid}"

    def __str__(self) -> str:
        return self.name

    def copy_attrs(self, new: Node):
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


class Instruction(Node):
    """Abstract base class for module-specific instructions"""

    def __init__(self, ln: int, c: List[Node]):
        super().__init__(ln, c)


class TLInstruction(Instruction):
    """Abstract base class for AST nodes that have valid TL assembly instructions"""

    def __init__(self, ln: int, c: List[Node]):
        super().__init__(ln, c)
        self.scq_size = 1

    def ftid_str(self) -> str:
        if self.ftid < 0:
            logger.critical(f" Node '{self}' never assigned ftid.")
            return ""
        return f"n{self.ftid}"

    def ptid_str(self) -> str:
        if self.ptid < 0:
            logger.critical(f" Node '{self}' never assigned ptid.")
            return ""
        return f"n{self.ptid}"
    
    def bzid_str(self) -> str:
        if self.bzid < 0:
            logger.critical(f" Node '{self}' never assigned bzid.")
            return ""
        return f"b{self.bzid}"
    
    def ft_asm(self) -> str:
        s = f"{self.ftid_str()} {self.name} "
        for child in self.get_children():
            s += f"{child.ftid_str()} "
        return s
    
    def pt_asm(self) -> str:
        s = f"{self.ptid_str()} {self.name} "
        for child in self.get_children():
            s += f"{child.ptid_str()} "
        return s
 
    def bz_asm(self) -> str:
        s = f"{self.bzid_str()} {self.name} "
        for child in self.get_children():
            s += f"{child.bzid_str()} "
        s += f"{self.atid_str()}" if self.atid >= 0 else ""
        return s


class BZInstruction(Instruction):
    """Abstract base class for AST nodes that have valid BZ assembly instructions"""

    def __init__(self, ln: int, c: List[Node]):
        super().__init__(ln, c)

    def ftid_str(self) -> str:
        if self.ftid < 0:
            logger.critical(f" Node '{self}' never assigned ftid.")
            return ""
        return f"n{self.ftid}"

    def ptid_str(self) -> str:
        if self.ptid < 0:
            logger.critical(f" Node '{self}' never assigned ptid.")
            return ""
        return f"n{self.ptid}"
    
    def bzid_str(self) -> str:
        if self.bzid < 0:
            logger.critical(f" Node '{self}' never assigned bzid.")
            return ""
        return f"b{self.bzid}"
    
    def ft_asm(self) -> str:
        return f"{self.ftid_str()} load {self.atid_str()}"
    
    def pt_asm(self) -> str:
        return f"{self.ptid_str()} load {self.atid_str()}"
 
    def bz_asm(self) -> str:
        s = f"{self.bzid_str()} {self.name} "
        for child in self.get_children():
            s += f"{child.bzid_str()} "
        s += f"{self.atid_str()}" if self.atid >= 0 else ""
        return s


class ATInstruction(Instruction):
    """Class for AST nodes that have valid AT assembly instructions"""

    def __init__(self, ln: int, n: str, f: str, a: List[Node], r: RelationalOperator, c: Node):
        super().__init__(ln, []) 
        self.name: str = n
        self.filter: str = f
        self.args: List[Node] = a
        self.rel_op: RelationalOperator = r
        self.compare: Node = c

    def __str__(self) -> str:
        s: str = f"{self.filter}("
        for arg in self.args:
            s += f"{arg.name},"
        s = s[:-1] + ") "
        s += f"{self.rel_op.name} {self.compare.name}"
        return s

    def at_asm(self) -> str:
        s: str = f"a{self.atid} {self.filter}("
        for arg in self.args:
            s += f"s{arg.sid}," if isinstance(arg, Signal) else f"{arg.name},"
        s = s[:-1] + ") "
        s += f"{self.rel_op.name} "
        s += f"s{self.compare.sid} " if isinstance(self.compare, Signal) else f"{self.compare.name}"
        return s
    
    def atid_str(self) -> str:
        if self.atid < 0:
            logger.critical(f" Node '{self}' never assigned atid.")
            return ""
        return f"a{self.atid}"


class Literal(Node):

    def __init__(self, ln: int, a: List[Node]):
        super().__init__(ln,[])


class Constant(Literal):

    def __init__(self, ln: int, a: List[Node]):
        super().__init__(ln,[])
        self.value = 0

    def get_value(self) -> int|float:
        return self.value


class Integer(Constant, BZInstruction):

    def __init__(self, ln: int, v: int):
        super().__init__(ln,[])
        self.value: int = v
        self.name = str(v)
        self.type = INT(True)

        if v.bit_length() > INT.width:
            logger.error(f"{ln} Constant \"{v}\" not representable in configured int width (\"{INT.width}\").")

    def get_value(self) -> int:
        return self.value

    def __deepcopy__(self, memo):
        new = Integer(self.ln, self.value)
        self.copy_attrs(new)
        return new

    def bz_asm(self) -> str:
        return f"{self.bzid_str()} iconst {self.value}"


class Float(Constant, BZInstruction):

    def __init__(self, ln: int, v: float):
        super().__init__(ln,[])
        self.type = FLOAT(True)
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

    def bz_asm(self) -> str:
        return f"{self.bzid_str()} fconst {self.value}"


class Variable(Node):
    """AST node representing a bound variable in set aggregation expressions"""

    def __init__(self, ln: int, n: str):
        super().__init__(ln,[])
        self.name: str = n

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Variable) and __o.name == self.name


class Signal(Literal, BZInstruction):

    def __init__(self, ln: int, n: str, t: Type):
        super().__init__(ln,[])
        self.name: str = n
        self.type: Type = t
        self.sid = -1

    def __deepcopy__(self, memo):
        copy = Signal(self.ln, self.name, self.type)
        copy.sid = self.sid
        return copy

    def ft_asm(self) -> str:
        return f"{self.ftid_str()} load {self.atid_str()}"

    def pt_asm(self) -> str:
        return f"{self.ptid_str()} load {self.atid_str()}"
    
    def bz_asm(self) -> str:
        s = f"{self.bzid_str()} load s{self.sid}"
        s += f" {self.atid_str()}" if self.atid >= 0 else ""
        return s
    

class Atomic(Literal, TLInstruction):

    def __init__(self, ln: int, n: str):
        super().__init__(ln, [])
        self.name: str = n
        self.type: Type = BOOL(False)

    def __deepcopy__(self, memo):
        copy = Atomic(self.ln, self.name)
        self.copy_attrs(copy)
        return copy

    def ft_asm(self) -> str:
        return f"{self.ftid_str()} load a{self.atid}" 

    def pt_asm(self) -> str:
        return f"{self.ptid_str()} load a{self.atid}" 


class Bool(Constant):

    def __init__(self, ln: int, v: bool):
        super().__init__(ln,[])
        self.type = BOOL(True)
        self.bpd: int = 0
        self.wpd: int = 0
        self.value: bool = v
        self.name = str(v)

    def ftid_str(self) -> str:
        return self.name

    def ptid_str(self) -> str:
        return self.name

    # def asm(self) -> str:
    #     return "iconst " + ("0" if self.name == "False" else "1")


class Set(Node):

    def __init__(self, ln: int, m: List[Node]):
        super().__init__(ln, m)
        m.sort(key=lambda x: str(x))
        self.max_size: int = len(m)
        self.dynamic_size = None

    def get_max_size(self) -> int:
        return self.max_size

    def get_dynamic_size(self) -> Node | None:
        return self.dynamic_size

    def set_dynamic_size(self, s: Node):
        self.dynamic_size = s

    def __str__(self) -> str:
        s: str = "{"
        for m in self.get_children():
            s += str(m) + ","
        s = s[:-1] + "}"
        return s


class Struct(Node):

    def __init__(self, ln: int, n: str, m: Dict[str, int], c: List[Node]):
        super().__init__(ln, c)
        self.name: str = n
        self.members: Dict[str, int] = m

    def get_member(self, name: str) -> Node:
        return self.get_child(self.members[name])

    def get_members(self) -> Dict[str, int]:
        return self.members

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = Struct(self.ln, self.name, self.members, children)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s: str = ""
        s += self.name + "("
        for i,e in self.members.items():
            s += f"{i}={self.get_child(e)},"
        s = s[:-1] + ")"
        return s


class StructAccess(Node):

    def __init__(self, ln: int, s: Node, m: str):
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


class Operator(Node):

    def __init__(self, ln: int, c: List[Node]):
        super().__init__(ln, c)
        self.arity: int = len(c)


class UnaryOperator(Operator):

    def __init__(self, ln: int, o: List[Node]):
        if len(o) != 1:
            logger.critical(f" '{type(self)}' requires exactly one child node.")
        super().__init__(ln, o)

    def get_operand(self) -> Node:
        return self.get_child(0)

    def __str__(self) -> str:
        return f"{self.symbol}({self.get_operand()})"


class BinaryOperator(Operator):

    def __init__(self, ln: int, l: List[Node]):
        if len(l) != 2:
            logger.critical(f" '{type(self)}' requires exactly two child nodes.")
        super().__init__(ln, l)

    def get_lhs(self) -> Node:
        return self.get_child(0)

    def get_rhs(self) -> Node:
        return self.get_child(1)

    def __str__(self) -> str:
        return f"({self.get_lhs()}){self.symbol}({self.get_rhs()})"


class Function(Operator):

    def __init__(self, ln: int, n: str, a: List[Node]):
        super().__init__(ln, a)
        self.name: str = n

    def __deepcopy__(self, memo):
        return Function(self.ln, self.name, deepcopy(self.get_children(), memo))

    def __str__(self) -> str:
        s = f"{self.name}("
        for arg in self._children:
            s += f"{arg},"
        return s[:-1] + ")"


class SetAggOperator(Operator):

    def __init__(self, ln: int, s: Set, v: Variable,  e: Node):
        super().__init__(ln, [s, v, e])

    def get_set(self) -> Set:
        return cast(Set, self.get_child(0))

    def get_boundvar(self) -> Variable:
        return cast(Variable, self.get_child(1))

    def get_expr(self) -> Node:
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

    def __init__(self, ln: int, s: Set, v: Variable, e: Node):
        super().__init__(ln, s, v, e)
        self.name: str = "foreach"


class ForSome(SetAggOperator):

    def __init__(self, ln: int, s: Set, v: Variable, e: Node):
        super().__init__(ln, s, v, e)
        self.name: str = "forsome"


class ForExactlyN(SetAggOperator):

    def __init__(self, ln: int, s: Set, n: Node, v: Variable, e: Node):
        super().__init__(ln, s, v, e)
        self.name: str = "forexactlyn"
        self.add_child(n)

    def get_num(self) -> Node:
        return self.get_child(3)
    
    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ForExactlyN(self.ln, cast(Set, children[0]), children[3], cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class ForAtLeastN(SetAggOperator):

    def __init__(self, ln: int, s: Set, n: Node, v: Variable, e: Node):
        super().__init__(ln, s, v, e)
        self.name: str = "foratleastn"
        self.add_child(n)

    def get_num(self) -> Node:
        return self.get_child(3)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ForExactlyN(self.ln, cast(Set, children[0]), children[3], cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class ForAtMostN(SetAggOperator):

    def __init__(self, ln: int, s: Set, n: Node, v: Variable, e: Node):
        super().__init__(ln, s, v, e)
        self.name: str = "foratmostn"
        self.add_child(n)

    def get_num(self) -> Node:
        return self.get_child(3)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ForExactlyN(self.ln, cast(Set, children[0]), children[3], cast(Variable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class Count(BZInstruction):

    def __init__(self, ln: int, n: Node, c: List[Node]):
        # Note: all members of c must be of type Boolean
        super().__init__(ln, c)
        self.num: Node = n
        self.name = "count"

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


class BitwiseOperator(Operator):

    def __init__(self, ln: int, c: List[Node]):
        super().__init__(ln, c)


class BitwiseAnd(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "bwand"
        self.symbol = "&"

    def __deepcopy__(self, memo):
        children = [cast(BZInstruction, deepcopy(c, memo)) for c in self._children]
        new = BitwiseAnd(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseOr(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "bwor"
        self.symbol = "|"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseOr(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseXor(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "bwxor"
        self.symbol = "^"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseShiftLeft(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "lshift"
        self.symbol = "<<"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseShiftLeft(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseShiftRight(BitwiseOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "rshift"
        self.symbol = ">>"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseShiftRight(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseNegate(BitwiseOperator, UnaryOperator, BZInstruction):

    def __init__(self, ln: int, o: Node):
        super().__init__(ln, [o])
        self.name = "bwneg"
        self.symbol = "~"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = BitwiseNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new


class ArithmeticOperator(Operator):

    def __init__(self, ln: int, c: List[Node]):
        super().__init__(ln, c)

    def __str__(self) -> str:
        s = f"{self.get_child(0)}"
        for c in range(1,len(self._children)):
            s += f"{self.symbol}{self.get_child(c)}"
        return s


class ArithmeticAdd(ArithmeticOperator, BZInstruction):

    def __init__(self, ln: int, c: List[Node]):
        # force binary operator for now
        if len(c) > 2:
            prev = ArithmeticAdd(ln, c[0:2])
            for i in range(2,len(c)-1):
                prev = ArithmeticAdd(ln, [prev,c[i]])
            super().__init__(ln, [prev,c[len(c)-1]])
            self.type = c[0].type
        else:
            super().__init__(ln, c)
            self.type = c[0].type

        self.name = "add"
        self.symbol = "+"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticAdd(self.ln, children)
        self.copy_attrs(new)
        return new


class ArithmeticSubtract(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "sub"
        self.symbol = "-"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticSubtract(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticMultiply(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "mul"
        self.symbol = "*"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticMultiply(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticDivide(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "div"
        self.symbol = "/"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticDivide(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticModulo(ArithmeticOperator, BinaryOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "mod"
        self.symbol = "%"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticModulo(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticNegate(UnaryOperator, ArithmeticOperator, BZInstruction):

    def __init__(self, ln: int, o: Node):
        super().__init__(ln, [o])
        self.name: str = "neg"
        self.symbol = "-"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = ArithmeticNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new


class RelationalOperator(BinaryOperator):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class Equal(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, lhs, rhs)
        self.name = "eq"
        self.symbol = "=="


class NotEqual(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, lhs, rhs)
        self.name = "neq"
        self.symbol = "!="


class GreaterThan(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, lhs, rhs)
        self.name = "gt"
        self.symbol = ">"


class LessThan(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, lhs, rhs)
        self.name = "lt"
        self.symbol = "<"


class GreaterThanOrEqual(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, lhs, rhs)
        self.name = "geq"
        self.symbol = ">="


class LessThanOrEqual(RelationalOperator, BZInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, lhs, rhs)
        self.name = "leq"
        self.symbol = "<="


class LogicalOperator(Operator):

    def __init__(self, ln: int, c: List[Node]):
        super().__init__(ln, c)
        self.bpd = min([child.bpd for child in c])
        self.wpd = max([child.wpd for child in c])


class LogicalOr(LogicalOperator, TLInstruction):

    def __init__(self, ln: int, c: List[Node]):
        # force binary operator for now
        if len(c) > 2:
            prev = LogicalOr(ln, c[0:2])
            for i in range(2,len(c)-1):
                prev = LogicalOr(ln, [prev,c[i]])
            super().__init__(ln, [prev,c[len(c)-1]])
        else:
            super().__init__(ln, c)

        super().__init__(ln, c)
        self.name = "or"
        self.symbol = "||"

    def __str__(self) -> str:
        s: str = ""
        for arg in self.get_children():
            s += str(arg) + "||"
        return s[:-2]


class LogicalAnd(LogicalOperator, TLInstruction):

    def __init__(self, ln: int, c: List[Node]):
        # force binary operator for now
        if len(c) > 2:
            prev = LogicalAnd(ln, c[0:2])
            for i in range(2,len(c)-1):
                prev = LogicalAnd(ln, [prev,c[i]])
            super().__init__(ln, [prev,c[len(c)-1]])
        else:
            super().__init__(ln, c)

        self.name = "and"
        self.symbol = "&&"

    def __str__(self) -> str:
        s: str = ""
        for arg in self.get_children():
            s += str(arg) + "&&"
        return s[:-2]


class LogicalXor(LogicalOperator, BinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "xor"
        self.symbol = "^^"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class LogicalImplies(LogicalOperator, BinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "impl"
        self.symbol = "->"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalImplies(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class LogicalIff(LogicalOperator, BinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node):
        super().__init__(ln, [lhs, rhs])
        self.name = "iff"
        self.symbol = "<->"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalIff(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class LogicalNegate(LogicalOperator, UnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: Node):
        super().__init__(ln, [o])
        self.name = "not"
        self.symbol = "!"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = LogicalNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new


class TemporalOperator(Operator):

    def __init__(self, ln: int, c: List[Node], l: int, u: int):
        super().__init__(ln, c)
        self.interval = Interval(lb=l,ub=u)


class FutureTimeOperator(TemporalOperator):

    def __init__(self, ln: int, c: List[Node], l: int, u: int):
        super().__init__(ln, c, l, u)


class PastTimeOperator(TemporalOperator):

    def __init__(self, ln: int, c: List[Node], l: int, u: int):
        super().__init__(ln, c, l, u)


# cannot inherit from BinaryOperator due to multiple inheriting classes
# with different __init__ signatures
class FutureTimeBinaryOperator(TemporalOperator):

    def __init__(self, ln: int, lhs: Node, rhs: Node, l: int, u: int):
        super().__init__(ln, [lhs, rhs], l, u)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def get_lhs(self) -> Node:
        return self.get_child(0)

    def get_rhs(self) -> Node:
        return self.get_child(1)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.get_lhs()!s}){self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"


class Until(FutureTimeBinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node, l: int, u: int):
        super().__init__(ln, lhs, rhs, l, u)
        self.name = "until"
        self.symbol = "U"

    def ft_asm(self) -> str:
        return f"{super().ftid_str()} {self.name} {self.get_lhs().ftid_str()} {self.get_rhs().ftid_str()} {self.interval.lb} {self.interval.ub}"


class Release(FutureTimeBinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node, l: int, u: int):
        super().__init__(ln, lhs, rhs, l, u)
        self.name = "release"
        self.symbol = "R"

    def ft_asm(self) -> str:
        return f"{super().ftid_str()} {self.name} {self.get_lhs().ftid_str()} {self.get_rhs().ftid_str()} {self.interval.lb} {self.interval.ub}"


class FutureTimeUnaryOperator(FutureTimeOperator):

    def __init__(self, ln: int, o: Node, l: int, u: int):
        super().__init__(ln, [o], l, u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def get_operand(self) -> Node:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"


class Global(FutureTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: Node, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.name = "global"
        self.symbol = "G"

    def ft_asm(self) -> str:
        return f"{super().ftid_str()} {self.name} {self.get_operand().ftid_str()} {self.interval.lb} {self.interval.ub}"


class Future(FutureTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: Node, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.name = "future"
        self.symbol = "F"

    def ft_asm(self) -> str:
        return f"{super().ftid_str()} {self.name} {self.get_operand().ftid_str()} {self.interval.lb} {self.interval.ub}"


class PastTimeBinaryOperator(PastTimeOperator):

    def __init__(self, ln: int, lhs: Node, rhs: Node, l: int, u: int):
        super().__init__(ln, [lhs, rhs], l, u)

    def get_lhs(self) -> Node:
        return self.get_child(0)

    def get_rhs(self) -> Node:
        return self.get_child(1)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.get_lhs()!s}){self.name!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"


class Since(PastTimeBinaryOperator, TLInstruction):

    def __init__(self, ln: int, lhs: Node, rhs: Node, l: int, u: int):
        super().__init__(ln, lhs, rhs, l, u)
        self.name = "since"
        self.symbol = "S"

    def pt_asm(self) -> str:
        return f"{super().ptid_str()} {self.name} {self.get_lhs().ptid_str()} {self.get_rhs().ptid_str()} {self.interval.lb} {self.interval.ub}"


class PastTimeUnaryOperator(PastTimeOperator):

    def __init__(self, ln: int, o: Node, l: int, u: int):
        super().__init__(ln, [o], l, u)

    def get_operand(self) -> Node:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"


class Historical(PastTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: Node, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.name = "hist"
        self.symbol = "H"

    def pt_asm(self) -> str:
        return f"{super().ptid_str()} {self.name} {self.get_operand().ptid_str()} {self.interval.lb} {self.interval.ub}"


class Once(PastTimeUnaryOperator, TLInstruction):

    def __init__(self, ln: int, o: Node, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.name = "once"
        self.symbol = "O"

    def pt_asm(self) -> str:
        return f"{super().ptid_str()} {self.name} {self.get_operand().ptid_str()} {self.interval.lb} {self.interval.ub}"


class Specification(TLInstruction):

    def __init__(self, ln: int, lbl: str, f: int, e: Node):
        super().__init__(ln, [e])
        self.name: str = lbl
        self.formula_number: int = f

    def get_expr(self) -> Node:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = Specification(self.ln, self.name, self.formula_number, children[0])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return (str(self.formula_number) if self.name == "" else self.name) + ": " + str(self.get_expr())

    def ft_asm(self) -> str:
        return f"{self.ftid_str()} end {self.get_expr().ftid_str()} f{self.formula_number}"

    def pt_asm(self) -> str:
        return f"{self.ptid_str()} end {self.get_expr().ptid_str()} f{self.formula_number}"


class Contract(Node):

    def __init__(self, ln: int, lbl: str, f1: int, f2: int, f3: int, a: TLInstruction, g: TLInstruction):
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

    def __init__(self, ln: int, t: FormulaType, s: List[Specification|Contract]):
        super().__init__(ln, [cast(Node, spec) for spec in s])
        self.formula_type = t

    def __str__(self) -> str:
        ret: str = f"{self.formula_type.name} Specs:\n"
        for s in self.get_children():
            ret += f"\t{s}\n"
        if len(self._children) == 0:
            ret += f"\tempty\n"
        return ret[:-1]

    def ft_asm(self) -> str:
        return f"{super().ftid_str()} endsequence"

    def pt_asm(self) -> str:
        return f"{super().ptid_str()} endsequence"


class Program(Node):

    def __init__(self, ln: int, sigs: Dict[str, Type], defs: Dict[str, Node], st: StructDict, a: Dict[str, Node], fts: SpecificationSet, pts: SpecificationSet):
        super().__init__(ln, [fts, pts])

        # Data
        self.timestamp_width: int = 0
        self.structs: StructDict = st
        self.signals: Dict[str, Type] = sigs
        self.definitions: Dict[str, Node] = defs
        self.atomics: Dict[str, Node] = a
        self.ft_spec_set: SpecificationSet = fts
        self.pt_spec_set: SpecificationSet = pts
        self.assembly: List[Instruction] = []
        self.scq_assembly: List[tuple[int,int]] = []
        self.signal_mapping: Dict[str,int] = {}
        self.contracts: Dict[str,tuple[int,int,int]] = {}
        self.implementation: R2U2Implementation = R2U2Implementation.C

        # Computable properties
        self.total_memory: int = -1
        self.cpu_wcet: float = -1
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
        s: Node
        for s in self.get_children():
            ret += str(s) + "\n"
        return ret[:-1]

    def __deepcopy__(self, memo):
        return Program(
            self.ln, 
            deepcopy(self.signals, memo), 
            deepcopy(self.definitions, memo), 
            deepcopy(self.structs, memo), 
            deepcopy(self.atomics, memo), 
            deepcopy(self.ft_spec_set, memo),
            deepcopy(self.pt_spec_set, memo)
        )
