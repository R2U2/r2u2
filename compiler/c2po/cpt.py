"""C2PO Parse Tree (CPT) represents structure of a .c2po or .mltl file."""

from __future__ import annotations
from typing import Optional, Union, cast
from copy import deepcopy
import pickle
from enum import Enum

from c2po import log
from c2po import types


class C2POSection(Enum):
    STRUCT = 0
    INPUT = 1
    DEFINE = 2
    ATOMIC = 3
    FTSPEC = 4
    PTSPEC = 5


class Node:
    def __init__(self, ln: int, c: list[Node]) -> None:
        self.ln: int = ln
        self.symbol: str = ""

        self.children: list[Node] = []
        self.parents: list[Node] = []

        for child in c:
            self.children.append(child)
            child.parents.append(self)

    def get_siblings(self) -> list[Node]:
        siblings = []

        for parent in self.parents:
            for sibling in [s for s in parent.children]:
                if sibling in siblings:
                    continue
                if sibling == self:
                    continue
                siblings.append(sibling)

        return siblings

    def num_children(self) -> int:
        return len(self.children)

    def num_parents(self) -> int:
        return len(self.parents)

    def get_child(self, i: int) -> Optional[Node]:
        if i >= self.num_children() or i < 0:
            return None
        return self.children[i]

    def get_parent(self, i: int) -> Optional[Node]:
        if i >= self.num_parents() or i < 0:
            return None
        return self.parents[i]

    def add_child(self, child: Node) -> None:
        self.children.append(child)
        child.parents.append(self)

    def remove_child(self, child: Node) -> None:
        self.children.remove(child)
        child.parents.remove(self)

    def replace(self, new: Node) -> None:
        """Replaces 'self' with 'new', setting the parents' children of 'self' to 'new'. Note that 'self' is orphaned as a result."""
        # Special case: if trying to replace this with itself
        if id(self) == id(new):
            return

        for parent in self.parents:
            for i in range(0, len(parent.children)):
                if id(parent.children[i]) == id(self):
                    parent.children[i] = new

            new.parents.append(parent)

        for child in self.children:
            if self in child.parents:
                child.parents.remove(self)

    def __str__(self) -> str:
        return self.symbol

    def copy_attrs(self, new: Node) -> None:
        new.symbol = self.symbol

    def __deepcopy__(self, memo) -> Node:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(self.ln, children)
        self.copy_attrs(new)
        return new


class Expression(Node):
    def __init__(self, ln: int, c: list[Node]) -> None:
        super().__init__(ln, c)
        self.engine = types.R2U2Engine.NONE
        self.atomic_id: int = -1  # only set for atomic propositions
        self.total_scq_size: int = -1
        self.scq_size: int = -1
        self.bpd: int = 0
        self.wpd: int = 0
        self.scq: tuple[int, int] = (-1, -1)
        self.type: types.Type = types.NoType()

    def get_siblings(self) -> list[Expression]:
        return cast("list[Expression]", super().get_siblings())

    def get_children(self) -> list[Expression]:
        return cast("list[Expression]", self.children)

    def copy_attrs(self, new: Expression) -> None:
        super().copy_attrs(new)
        new.scq_size = self.scq_size
        new.bpd = self.bpd
        new.wpd = self.wpd
        new.type = self.type

    def to_mltl_std(self) -> str:
        if self.atomic_id < 0:
            raise TypeError(
                f"{self.ln}: Non-atomic node type '{type(self)}' unsupported in MLTL standard."
            )
        return f"a{self.atomic_id}"


class Literal(Expression):
    def __init__(self, ln: int) -> None:
        super().__init__(ln, [])

    def __str__(self) -> str:
        return self.symbol


class Constant(Literal):
    def __init__(self, ln: int, a: list[Node]) -> None:
        super().__init__(ln)
        self.value = 0

    def get_value(self) -> Union[int, float]:
        return self.value


class Bool(Constant):
    def __init__(self, ln: int, v: bool) -> None:
        super().__init__(ln, [])
        self.type = types.BoolType(True)
        self.bpd: int = 0
        self.wpd: int = 0
        self.value: bool = v
        self.symbol = str(v)
        self.engine = types.R2U2Engine.BOOLEANIZER

    def to_mltl_std(self) -> str:
        return self.symbol.lower()


class Integer(Constant):
    def __init__(self, ln: int, v: int) -> None:
        super().__init__(ln, [])
        self.value: int = v
        self.symbol = str(v)
        self.type = types.IntType(True)
        self.engine = types.R2U2Engine.BOOLEANIZER

        if v.bit_length() > types.IntType.width:
            log.logger.error(
                f"{ln} Constant '{v}' not representable in configured int width ('{types.IntType.width}')."
            )

    def get_value(self) -> int:
        return self.value

    def __deepcopy__(self, memo) -> Integer:
        new = Integer(self.ln, self.value)
        self.copy_attrs(new)
        return new


class Float(Constant):
    def __init__(self, ln: int, v: float) -> None:
        super().__init__(ln, [])
        self.type = types.FloatType(True)
        self.value: float = v
        self.symbol = str(v)
        self.engine = types.R2U2Engine.BOOLEANIZER

        # FIXME:
        # if len(v.hex()[2:]) > FLOAT.width:
        #     log.logger.error(f"{ln} Constant '{v}' not representable in configured float width ('{FLOAT.width}').")

    def get_value(self) -> float:
        return self.value

    def __deepcopy__(self, memo) -> Float:
        new = Float(self.ln, self.value)
        self.copy_attrs(new)
        return new


class Variable(Expression):
    def __init__(self, ln: int, s: str) -> None:
        super().__init__(ln, [])
        self.symbol: str = s

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Variable) and __o.symbol == self.symbol

    def __hash__(self) -> int:
        # note how this compares to __eq__
        # we hash the id so that in sets/dicts different
        # instances of the same variable are distinct
        return id(self)

    def __str__(self) -> str:
        return self.symbol


class Signal(Literal):
    def __init__(self, ln: int, s: str, t: types.Type) -> None:
        super().__init__(ln)
        self.symbol: str = s
        self.type: types.Type = t
        self.signal_id: int = -1
        self.engine = types.R2U2Engine.BOOLEANIZER

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Signal) and __o.symbol == self.symbol

    def __hash__(self) -> int:
        return id(self)

    def __deepcopy__(self, memo) -> Signal:
        copy = Signal(self.ln, self.symbol, self.type)
        return copy


class AtomicChecker(Literal):
    def __init__(self, ln: int, s: str) -> None:
        super().__init__(ln)
        self.symbol: str = s
        self.type: types.Type = types.BoolType(False)
        self.engine = types.R2U2Engine.ATOMIC_CHECKER

    def __deepcopy__(self, memo) -> AtomicChecker:
        copy = AtomicChecker(self.ln, self.symbol)
        self.copy_attrs(copy)
        return copy


class SetExpression(Expression):
    def __init__(self, ln: int, m: list[Node]) -> None:
        super().__init__(ln, m)
        m.sort(key=lambda x: str(x))
        self.max_size: int = len(m)
        self.dynamic_size = None

    def get_members(self) -> list[Expression]:
        return cast("list[Expression]", self.children)

    def get_max_size(self) -> int:
        return self.max_size

    def get_dynamic_size(self) -> Union[Node, None]:
        return self.dynamic_size

    def set_dynamic_size(self, s: Node) -> None:
        self.dynamic_size = s

    def __str__(self) -> str:
        s: str = "{"
        for m in self.children:
            s += str(m) + ","
        s = s[:-1] + "}"
        return s


class Struct(Expression):
    def __init__(self, ln: int, s: str, m: dict[str, int], c: list[Node]) -> None:
        super().__init__(ln, c)
        self.symbol: str = s

        # hack to get named arguments -- see get_member
        # cannot use *just* members, else the parent tracking breaks
        self.members: dict[str, int] = m

    def get_member(self, name: str) -> Optional[Expression]:
        member = self.get_child(self.members[name])
        if member is None:
            return None
        return cast(Expression, member)

    def get_members(self) -> list[Expression]:
        return cast("list[Expression]", self.children)

    def __deepcopy__(self, memo) -> Struct:
        children = [deepcopy(c, memo) for c in self.children]
        new = Struct(self.ln, self.symbol, self.members, children)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s = self.symbol + "("
        s += ",".join([f"{i}={self.get_child(e)}" for i, e in self.members.items()])
        s += ")"
        return s


class StructAccess(Expression):
    def __init__(self, ln: int, s: Node, m: str) -> None:
        super().__init__(ln, [s])
        self.member: str = m

    def get_struct(self) -> Struct:
        return cast(Struct, self.get_child(0))

    def __deepcopy__(self, memo) -> StructAccess:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(self.ln, children[0], self.member)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return str(self.get_struct()) + "." + self.member


class Operator(Expression):
    def __init__(self, ln: int, c: list[Node]) -> None:
        super().__init__(ln, c)
        self.arity: int = len(c)

    def get_operands(self) -> list[Expression]:
        return cast("list[Expression]", self.children)

    def get_operand(self, i: int) -> Expression:
        return cast(Expression, self.get_child(i))


class UnaryOperator(Operator):
    def __init__(self, ln: int, o: list[Node]) -> None:
        if len(o) != 1:
            raise ValueError(f" '{type(self)}' requires exactly one child node.")
        super().__init__(ln, o)

    def get_operand(self) -> Expression:
        # FIXME: Does this work if we override the above get_operand?
        return cast(Expression, self.get_child(0))

    def __str__(self) -> str:
        return f"{self.symbol}({self.get_operand()})"


class BinaryOperator(Operator):
    def __init__(self, ln: int, operands: list[Node]) -> None:
        if len(operands) != 2:
            raise ValueError(f"'{type(self)}' requires exactly two child nodes.")
        super().__init__(ln, operands)

    def get_lhs(self) -> Expression:
        return self.get_operand(0)

    def get_rhs(self) -> Expression:
        return self.get_operand(1)

    def __str__(self) -> str:
        return f"({self.get_lhs()}){self.symbol}({self.get_rhs()})"


class FunctionCall(Operator):
    def __init__(self, ln: int, s: str, a: list[Node]) -> None:
        super().__init__(ln, a)
        self.symbol: str = s

    def __deepcopy__(self, memo) -> FunctionCall:
        return FunctionCall(
            self.ln, self.symbol, deepcopy(cast("list[Node]", self.children), memo)
        )

    def __str__(self) -> str:
        s = f"{self.symbol}("
        for arg in self.children:
            s += f"{arg},"
        return s[:-1] + ")"


class SetAggOperator(Operator):
    def __init__(self, ln: int, s: SetExpression, v: Variable, e: Node) -> None:
        super().__init__(ln, [s, v, e])

    def get_set(self) -> SetExpression:
        return cast(SetExpression, self.get_child(0))

    def get_boundvar(self) -> Variable:
        return cast(Variable, self.get_child(1))

    def get_expr(self) -> Expression:
        return cast(Expression, self.get_child(2))

    def __deepcopy__(self, memo) -> SetAggOperator:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(
            self.ln,
            cast(SetExpression, children[0]),
            cast(Variable, children[1]),
            children[2],
        )
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return (
            self.symbol
            + "("
            + str(self.get_boundvar())
            + ":"
            + str(self.get_set())
            + ")"
            + "("
            + str(self.get_expr())
            + ")"
        )


class ForEach(SetAggOperator):
    def __init__(self, ln: int, s: SetExpression, v: Variable, e: Node) -> None:
        super().__init__(ln, s, v, e)
        self.symbol: str = "foreach"


class ForSome(SetAggOperator):
    def __init__(self, ln: int, s: SetExpression, v: Variable, e: Node) -> None:
        super().__init__(ln, s, v, e)
        self.symbol: str = "forsome"


class ForExactly(SetAggOperator):
    def __init__(
        self, ln: int, s: SetExpression, n: Node, v: Variable, e: Node
    ) -> None:
        super().__init__(ln, s, v, e)
        self.symbol: str = "forexactly"
        self.add_child(n)

    def get_num(self) -> Expression:
        return cast(Expression, self.get_child(3))

    def __deepcopy__(self, memo) -> ForExactly:
        children = [deepcopy(c, memo) for c in self.children]
        new = ForExactly(
            self.ln,
            cast(SetExpression, children[0]),
            children[3],
            cast(Variable, children[1]),
            children[2],
        )
        self.copy_attrs(new)
        return new


class ForAtLeast(SetAggOperator):
    def __init__(
        self, ln: int, s: SetExpression, n: Node, v: Variable, e: Node
    ) -> None:
        super().__init__(ln, s, v, e)
        self.symbol: str = "foratleast"
        self.add_child(n)

    def get_num(self) -> Expression:
        return cast(Expression, self.get_child(3))

    def __deepcopy__(self, memo) -> ForAtLeast:
        children = [deepcopy(c, memo) for c in self.children]
        new = ForAtLeast(
            self.ln,
            cast(SetExpression, children[0]),
            children[3],
            cast(Variable, children[1]),
            children[2],
        )
        self.copy_attrs(new)
        return new


class ForAtMost(SetAggOperator):
    def __init__(
        self, ln: int, s: SetExpression, n: Node, v: Variable, e: Node
    ) -> None:
        super().__init__(ln, s, v, e)
        self.symbol: str = "foratmost"
        self.add_child(n)

    def get_num(self) -> Expression:
        return cast(Expression, self.get_child(3))

    def __deepcopy__(self, memo) -> ForAtMost:
        children = [deepcopy(c, memo) for c in self.children]
        new = ForAtMost(
            self.ln,
            cast(SetExpression, children[0]),
            children[3],
            cast(Variable, children[1]),
            children[2],
        )
        self.copy_attrs(new)
        return new


class Count(Operator):
    def __init__(self, ln: int, n: Node, c: list[Node]) -> None:
        # Note: all members of c must be of type Boolean
        super().__init__(ln, c)
        self.num: Node = n
        self.name = "count"

    def __deepcopy__(self, memo) -> Count:
        children = [deepcopy(c, memo) for c in self.children]
        if len(children) > 1:
            new = Count(self.ln, children[0], children[1:])
        else:
            new = Count(self.ln, children[0], [])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s = "count("
        for c in self.children:
            s += str(c) + ","
        return s[:-1] + ")"


class BitwiseOperator(Operator):
    def __init__(self, ln: int, c: list[Node]) -> None:
        super().__init__(ln, c)
        self.engine = types.R2U2Engine.BOOLEANIZER


class BitwiseAnd(BitwiseOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "&"

    def __deepcopy__(self, memo) -> BitwiseAnd:
        children = [deepcopy(c, memo) for c in self.children]
        new = BitwiseAnd(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseOr(BitwiseOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "|"

    def __deepcopy__(self, memo) -> BitwiseOr:
        children = [deepcopy(c, memo) for c in self.children]
        new = BitwiseOr(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseXor(BitwiseOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "^"

    def __deepcopy__(self, memo) -> BitwiseXor:
        children = [deepcopy(c, memo) for c in self.children]
        new = BitwiseXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseShiftLeft(BitwiseOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "<<"

    def __deepcopy__(self, memo) -> BitwiseShiftLeft:
        children = [deepcopy(c, memo) for c in self.children]
        new = BitwiseShiftLeft(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseShiftRight(BitwiseOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = ">>"

    def __deepcopy__(self, memo) -> BitwiseShiftRight:
        children = [deepcopy(c, memo) for c in self.children]
        new = BitwiseShiftRight(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseNegate(BitwiseOperator, UnaryOperator):
    def __init__(self, ln: int, o: Node) -> None:
        super().__init__(ln, [o])
        self.symbol = "~"

    def __deepcopy__(self, memo) -> BitwiseNegate:
        children = [deepcopy(c, memo) for c in self.children]
        new = BitwiseNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new


class ArithmeticOperator(Operator):
    def __init__(self, ln: int, c: list[Node]) -> None:
        super().__init__(ln, c)
        self.engine = types.R2U2Engine.BOOLEANIZER

    def __str__(self) -> str:
        s = f"{self.get_child(0)}"
        for c in range(1, len(self.children)):
            s += f"{self.symbol}{self.get_child(c)}"
        return s


class ArithmeticAdd(ArithmeticOperator):
    def __init__(self, ln: int, c: list[Node]) -> None:
        # force binary operator for now
        if len(c) > 2:
            prev = ArithmeticAdd(ln, c[0:2])
            for i in range(2, len(c) - 1):
                prev = ArithmeticAdd(ln, [prev, c[i]])
            super().__init__(ln, [prev, c[len(c) - 1]])
            self.type = self.get_operand(0).type
        else:
            super().__init__(ln, c)
            self.type = self.get_operand(0).type

        self.symbol = "+"

    def __deepcopy__(self, memo) -> ArithmeticAdd:
        children = [deepcopy(c, memo) for c in self.children]
        new = ArithmeticAdd(self.ln, children)
        self.copy_attrs(new)
        return new


class ArithmeticSubtract(ArithmeticOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "-"

    def __deepcopy__(self, memo) -> ArithmeticSubtract:
        children = [deepcopy(c, memo) for c in self.children]
        new = ArithmeticSubtract(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticMultiply(ArithmeticOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "*"

    def __deepcopy__(self, memo) -> ArithmeticMultiply:
        children = [deepcopy(c, memo) for c in self.children]
        new = ArithmeticMultiply(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticDivide(ArithmeticOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "/"

    def __deepcopy__(self, memo) -> ArithmeticDivide:
        children = [deepcopy(c, memo) for c in self.children]
        new = ArithmeticDivide(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticModulo(ArithmeticOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "%"

    def __deepcopy__(self, memo) -> ArithmeticModulo:
        children = [deepcopy(c, memo) for c in self.children]
        new = ArithmeticModulo(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticNegate(UnaryOperator, ArithmeticOperator):
    def __init__(self, ln: int, o: Node) -> None:
        super().__init__(ln, [o])
        self.symbol = "-"

    def __deepcopy__(self, memo) -> ArithmeticNegate:
        children = [deepcopy(c, memo) for c in self.children]
        new = ArithmeticNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new


class RelationalOperator(BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.engine = types.R2U2Engine.BOOLEANIZER

    def __deepcopy__(self, memo) -> RelationalOperator:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class Equal(RelationalOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, lhs, rhs)
        self.symbol = "=="


class NotEqual(RelationalOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, lhs, rhs)
        self.symbol = "!="


class GreaterThan(RelationalOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, lhs, rhs)
        self.symbol = ">"


class LessThan(RelationalOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, lhs, rhs)
        self.symbol = "<"


class GreaterThanOrEqual(RelationalOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, lhs, rhs)
        self.symbol = ">="


class LessThanOrEqual(RelationalOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, lhs, rhs)
        self.symbol = "<="


class LogicalOperator(Operator):
    def __init__(self, ln: int, c: list[Node]) -> None:
        super().__init__(ln, c)
        self.bpd = min([child.bpd for child in self.get_operands()])
        self.wpd = max([child.wpd for child in self.get_operands()])
        self.engine = types.R2U2Engine.TEMPORAL_LOGIC


class LogicalOr(LogicalOperator):
    def __init__(self, ln: int, c: list[Node]) -> None:
        # force binary operator for now
        if len(c) > 2:
            prev = LogicalOr(ln, c[0:2])
            for i in range(2, len(c) - 1):
                prev = LogicalOr(ln, [prev, c[i]])
            super().__init__(ln, [prev, c[len(c) - 1]])
        else:
            super().__init__(ln, c)

        super().__init__(ln, c)
        self.symbol = "||"

    def __str__(self) -> str:
        return self.symbol.join([str(c) for c in self.get_operands()])

    def to_mltl_std(self) -> str:
        return "|".join([f"({c.to_mltl_std()})" for c in self.get_operands()])


class LogicalAnd(LogicalOperator):
    def __init__(self, ln: int, c: list[Node]) -> None:
        # force binary operator for now
        if len(c) > 2:
            prev = LogicalAnd(ln, c[0:2])
            for i in range(2, len(c) - 1):
                prev = LogicalAnd(ln, [prev, c[i]])
            super().__init__(ln, [prev, c[len(c) - 1]])
        else:
            super().__init__(ln, c)

        self.symbol = "&&"

    def __str__(self) -> str:
        return self.symbol.join([str(c) for c in self.get_operands()])

    def to_mltl_std(self) -> str:
        return "&".join([f"({c.to_mltl_std()})" for c in self.get_operands()])


class LogicalXor(LogicalOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "^^"

    def __deepcopy__(self, memo) -> LogicalXor:
        children = [deepcopy(c, memo) for c in self.children]
        new = LogicalXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class LogicalImplies(LogicalOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "->"

    def __deepcopy__(self, memo) -> LogicalImplies:
        children = [deepcopy(c, memo) for c in self.children]
        new = LogicalImplies(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()})->({self.get_rhs().to_mltl_std()})"


class LogicalIff(LogicalOperator, BinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node) -> None:
        super().__init__(ln, [lhs, rhs])
        self.symbol = "<->"

    def __deepcopy__(self, memo) -> LogicalIff:
        children = [deepcopy(c, memo) for c in self.children]
        new = LogicalIff(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()})<->({self.get_rhs().to_mltl_std()})"


class LogicalNegate(LogicalOperator, UnaryOperator):
    def __init__(self, ln: int, o: Node) -> None:
        super().__init__(ln, [o])
        self.symbol = "!"

    def __deepcopy__(self, memo) -> LogicalNegate:
        children = [deepcopy(c, memo) for c in self.children]
        new = LogicalNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def to_mltl_std(self) -> str:
        return f"!({self.get_operand().to_mltl_std()})"


class TemporalOperator(Operator):
    def __init__(self, ln: int, c: list[Node], lb: int, ub: int) -> None:
        super().__init__(ln, c)
        self.interval = types.Interval(lb=lb, ub=ub)
        self.engine = types.R2U2Engine.TEMPORAL_LOGIC


class FutureTimeOperator(TemporalOperator):
    def __init__(self, ln: int, c: list[Node], lb: int, ub: int) -> None:
        super().__init__(ln, c, lb, ub)


class PastTimeOperator(TemporalOperator):
    def __init__(self, ln: int, c: list[Node], lb: int, ub: int) -> None:
        super().__init__(ln, c, lb, ub)


# subclasses cannot inherit from BinaryOperator due to multiple inheriting classes
# with different __init__ signatures
class FutureTimeBinaryOperator(TemporalOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node, lb: int, ub: int) -> None:
        super().__init__(ln, [lhs, rhs], lb, ub)
        self.bpd = min(self.get_lhs().bpd, self.get_rhs().bpd) + self.interval.lb
        self.wpd = max(self.get_lhs().wpd, self.get_rhs().wpd) + self.interval.ub

    def get_lhs(self) -> Expression:
        return self.get_operand(0)

    def get_rhs(self) -> Expression:
        return self.get_operand(1)

    def __deepcopy__(self, memo) -> FutureTimeBinaryOperator:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(
            self.ln, children[0], children[1], self.interval.lb, self.interval.ub
        )
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.get_lhs()!s}){self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()}){self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_rhs().to_mltl_std()})"


class Until(FutureTimeBinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node, lb: int, ub: int) -> None:
        super().__init__(ln, lhs, rhs, lb, ub)
        self.symbol = "U"


class Release(FutureTimeBinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node, lb: int, ub: int) -> None:
        super().__init__(ln, lhs, rhs, lb, ub)
        self.symbol = "R"


class FutureTimeUnaryOperator(FutureTimeOperator):
    def __init__(self, ln: int, o: Node, lb: int, ub: int) -> None:
        super().__init__(ln, [o], lb, ub)
        self.bpd = self.get_operand().bpd + self.interval.lb
        self.wpd = self.get_operand().wpd + self.interval.ub

    def get_operand(self) -> Expression:
        return cast(Expression, self.get_child(0))

    def __deepcopy__(self, memo) -> FutureTimeUnaryOperator:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"

    def to_mltl_std(self) -> str:
        return f"{self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_operand().to_mltl_std()})"


class Global(FutureTimeUnaryOperator):
    def __init__(self, ln: int, o: Node, lb: int, ub: int) -> None:
        super().__init__(ln, o, lb, ub)
        self.symbol = "G"


class Future(FutureTimeUnaryOperator):
    def __init__(self, ln: int, o: Node, lb: int, ub: int) -> None:
        super().__init__(ln, o, lb, ub)
        self.symbol = "F"


class PastTimeBinaryOperator(PastTimeOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node, lb: int, ub: int) -> None:
        super().__init__(ln, [lhs, rhs], lb, ub)

    def get_lhs(self) -> Expression:
        return self.get_operand(0)

    def get_rhs(self) -> Expression:
        return self.get_operand(1)

    def __deepcopy__(self, memo) -> PastTimeBinaryOperator:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(
            self.ln, children[0], children[1], self.interval.lb, self.interval.ub
        )
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.get_lhs()!s}){self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()}){self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_rhs().to_mltl_std()})"


class Since(PastTimeBinaryOperator):
    def __init__(self, ln: int, lhs: Node, rhs: Node, lb: int, ub: int) -> None:
        super().__init__(ln, lhs, rhs, lb, ub)
        self.symbol = "S"


class PastTimeUnaryOperator(PastTimeOperator):
    def __init__(self, ln: int, o: Node, lb: int, ub: int) -> None:
        super().__init__(ln, [o], lb, ub)

    def get_operand(self) -> Expression:
        return cast(Expression, self.get_child(0))

    def __deepcopy__(self, memo) -> PastTimeUnaryOperator:
        children = [deepcopy(c, memo) for c in self.children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"

    def to_mltl_std(self) -> str:
        return f"{self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_operand().to_mltl_std()})"


class Historical(PastTimeUnaryOperator):
    def __init__(self, ln: int, o: Node, lb: int, ub: int) -> None:
        super().__init__(ln, o, lb, ub)
        self.symbol = "H"


class Once(PastTimeUnaryOperator):
    def __init__(self, ln: int, o: Node, lb: int, ub: int) -> None:
        super().__init__(ln, o, lb, ub)
        self.symbol = "O"


class Specification(Expression):
    def __init__(self, ln: int, lbl: str, f: int, e: Node) -> None:
        super().__init__(ln, [e])
        self.symbol: str = lbl
        self.formula_number: int = f
        self.engine = types.R2U2Engine.TEMPORAL_LOGIC

    def get_expr(self) -> Expression:
        return cast(Expression, self.get_child(0))

    def __deepcopy__(self, memo) -> Specification:
        children = [deepcopy(c, memo) for c in self.children]
        new = Specification(self.ln, self.symbol, self.formula_number, children[0])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return (
            (str(self.formula_number) if self.symbol == "" else self.symbol)
            + ": "
            + str(self.get_expr())
        )

    def to_mltl_std(self) -> str:
        return self.get_expr().to_mltl_std()


class Contract(Node):
    def __init__(
        self,
        ln: int,
        lbl: str,
        f1: int,
        f2: int,
        f3: int,
        a: Expression,
        g: Expression,
    ) -> None:
        super().__init__(ln, [a, g])
        self.symbol: str = lbl
        self.formula_numbers: tuple[int, int, int] = (f1, f2, f3)

    def get_assumption(self) -> Expression:
        return cast(Expression, self.get_child(0))

    def get_guarantee(self) -> Expression:
        return cast(Expression, self.get_child(1))

    def __str__(self) -> str:
        return f"({self.get_assumption()})=>({self.get_guarantee()})"

    def to_mltl_std(self) -> str:
        return f"({self.get_assumption})->({self.get_guarantee()})"


class StructDefinition(Node):
    def __init__(self, ln: int, symbol: str, m: list[Node]) -> None:
        super().__init__(ln, m)
        self.symbol = symbol
        self._members = {}
        for decl in cast("list[VariableDeclaration]", m):
            for sym in decl.get_symbols():
                self._members[sym] = decl.get_type()

    def get_declarations(self) -> list[VariableDeclaration]:
        return cast("list[VariableDeclaration]", self.children)

    def get_members(self) -> dict[str, types.Type]:
        return self._members

    def __str__(self) -> str:
        members_str_list = [str(s) + ";" for s in self.children]
        return self.symbol + "{" + " ".join(members_str_list) + ")"


class VariableDeclaration(Node):
    def __init__(self, ln: int, vars: list[str], t: types.Type) -> None:
        super().__init__(ln, [])
        self._variables = vars
        self._type = t

    def get_symbols(self) -> list[str]:
        return self._variables

    def get_type(self) -> types.Type:
        return self._type

    def __str__(self) -> str:
        return f"{','.join(self._variables)}: {str(self._type)}"


class Definition(Node):
    def __init__(self, ln: int, symbol: str, e: Expression) -> None:
        super().__init__(ln, [e])
        self.symbol = symbol

    def get_expr(self) -> Expression:
        return cast(Expression, self.get_child(0))

    def __str__(self) -> str:
        return f"{self.symbol} := {self.get_expr()}"


class AtomicCheckerDefinition(Node):
    def __init__(self, ln: int, symbol: str, e: Expression) -> None:
        super().__init__(ln, [e])
        self.symbol = symbol

    def get_expr(self) -> Expression:
        return cast(Expression, self.get_child(0))

    def __str__(self) -> str:
        return f"{self.symbol} := {self.get_expr()}"


class StructSection(Node):
    def __init__(self, ln: int, struct_defs: list[Node]) -> None:
        super().__init__(ln, struct_defs)

    def get_structs(self) -> list[StructDefinition]:
        return cast("list[StructDefinition]", self.children)

    def replace(self, node: Node) -> None:
        raise RuntimeError("Attempting to replace a C2POStructSection.")

    def __str__(self) -> str:
        structs_str_list = [str(s) + ";" for s in self.children]
        return "STRUCT\n\t" + "\n\t".join(structs_str_list)


class InputSection(Node):
    def __init__(self, ln: int, signal_decls: list[Node]) -> None:
        super().__init__(ln, signal_decls)

    def get_signals(self) -> list[VariableDeclaration]:
        return cast("list[VariableDeclaration]", self.children)

    def replace(self, node: Node) -> None:
        raise RuntimeError("Attempting to replace a C2POInputSection.")

    def __str__(self) -> str:
        signals_str_list = [str(s) + ";" for s in self.children]
        return "INPUT\n\t" + "\n\t".join(signals_str_list)


class DefineSection(Node):
    def __init__(self, ln: int, defines: list[Node]) -> None:
        super().__init__(ln, defines)

    def get_definitions(self) -> list[Definition]:
        return cast("list[Definition]", self.children)

    def replace(self, node: Node) -> None:
        raise RuntimeError("Attempting to replace a C2PODefineSection.")

    def __str__(self) -> str:
        defines_str_list = [str(s) + ";" for s in self.children]
        return "DEFINE\n\t" + "\n\t".join(defines_str_list)


class AtomicSection(Node):
    def __init__(self, ln: int, atomics: list[Node]):
        super().__init__(ln, atomics)

    def get_atomic_checkers(self) -> list[AtomicCheckerDefinition]:
        return cast("list[AtomicCheckerDefinition]", self.children)

    def replace(self, node: Node):
        raise RuntimeError("Attempting to replace a C2POAtomicSection.")

    def __str__(self) -> str:
        atomics_str_list = [str(s) + ";" for s in self.children]
        return "ATOMIC\n\t" + "\n\t".join(atomics_str_list)


class SpecSection(Node):
    def __init__(self, ln: int, s: list[Node]) -> None:
        super().__init__(ln, s)

    def get_specs(self) -> list[Union[Specification, Contract]]:
        return cast("list[Union[Specification, Contract]]", self.children)

    def replace(self, node: Node) -> None:
        raise RuntimeError("Attempting to replace a C2POSpecSection.")

    def __str__(self) -> str:
        spec_str_list = [str(s) + ";" for s in self.children]
        return "\n\t".join(spec_str_list)

    def to_mltl_std(self) -> str:
        return "\n".join([s.to_mltl_std() for s in self.get_specs()])


class FutureTimeSpecSection(SpecSection):
    def __init__(self, ln: int, s: list[Node]) -> None:
        super().__init__(ln, s)

    def __str__(self) -> str:
        return "FTPSEC\n\t" + super().__str__()


class PastTimeSpecSection(SpecSection):
    def __init__(self, ln: int, s: list[Node]) -> None:
        super().__init__(ln, s)

    def __str__(self) -> str:
        return "PTSPEC\n\t" + super().__str__()


class Program(Node):
    def __init__(self, ln: int, sections: list[Node]) -> None:
        super().__init__(ln, sections)

        self.future_time_spec_section_idx = -1
        self.past_time_spec_section_idx = -1

        for section in sections:
            if isinstance(section, FutureTimeSpecSection):
                self.future_time_spec_section_idx = sections.index(section)
            elif isinstance(section, PastTimeSpecSection):
                self.past_time_spec_section_idx = sections.index(section)

    def get_sections(self) -> list[C2POSection]:
        return cast("list[C2POSection]", self.children)

    def get_spec_sections(self) -> list[SpecSection]:
        return [s for s in self.children if isinstance(s, SpecSection)]

    def get_future_time_spec_section(self) -> Optional[FutureTimeSpecSection]:
        if self.future_time_spec_section_idx < 0:
            return None
        return cast(
            FutureTimeSpecSection, self.get_child(self.future_time_spec_section_idx)
        )

    def get_past_time_spec_section(self) -> Optional[PastTimeSpecSection]:
        if self.past_time_spec_section_idx < 0:
            return None
        return cast(
            PastTimeSpecSection, self.get_child(self.past_time_spec_section_idx)
        )

    def get_future_time_specs(self) -> list[Union[Specification, Contract]]:
        future_time_spec_section = self.get_future_time_spec_section()
        if future_time_spec_section:
            return future_time_spec_section.get_specs()
        return []

    def get_past_time_specs(self) -> list[Union[Specification, Contract]]:
        past_time_spec_section = self.get_past_time_spec_section()
        if past_time_spec_section:
            return past_time_spec_section.get_specs()
        return []

    def get_specs(self) -> list[Union[Specification, Contract]]:
        return self.get_future_time_specs() + self.get_past_time_specs()

    def replace(self, node: Node) -> None:
        raise RuntimeError("Attempting to replace a program.")

    def pickle(self) -> bytes:
        return pickle.dumps(self)

    def __str__(self) -> str:
        return "\n".join([str(s) for s in self.children])

    def to_mltl_std(self) -> str:
        return "\n".join([s.to_mltl_std() for s in self.get_specs()]) + "\n"


class Context:
    def __init__(
        self,
        impl: types.R2U2Implementation,
        mission_time: int,
        atomic_checkers: bool,
        booleanizer: bool,
        assembly_enabled: bool,
        signal_mapping: types.SignalMapping,
    ):
        self.definitions: dict[str, Expression] = {}
        self.structs: dict[str, dict[str, types.Type]] = {}
        self.signals: dict[str, types.Type] = {}
        self.variables: dict[str, types.Type] = {}
        self.atomic_checkers: dict[str, Expression] = {}
        self.specifications: dict[str, Specification] = {}
        self.contracts: dict[str, Contract] = {}
        self.atomics: set[Expression] = set()
        self.implementation = impl
        self.booleanizer_enabled = booleanizer
        self.atomic_checker_enabled = atomic_checkers
        self.mission_time = mission_time
        self.signal_mapping = signal_mapping
        self.assembly_enabled = assembly_enabled

        self.is_ft = False
        self.has_future_time = False
        self.has_past_time = False

        self.atomic_checker_filters: dict[str, list[types.Type]] = {
            "exactly_one_of": [types.SetType(False, types.BoolType(False))],
            "all_of": [types.SetType(False, types.BoolType(False))],
            "none_of": [types.SetType(False, types.BoolType(False))],
        }

    def get_symbols(self) -> list[str]:
        symbols = [s for s in self.definitions.keys()]
        symbols += [s for s in self.structs.keys()]
        symbols += [s for s in self.signals.keys()]
        symbols += [s for s in self.variables.keys()]
        symbols += [s for s in self.atomic_checkers.keys()]
        symbols += [s for s in self.specifications.keys()]
        symbols += [s for s in self.contracts.keys()]
        return symbols

    def is_future_time(self) -> bool:
        return self.is_ft

    def is_past_time(self) -> bool:
        return not self.is_ft

    def set_future_time(self) -> None:
        self.is_ft = True

    def set_past_time(self) -> None:
        self.is_ft = False

    def add_signal(self, symbol: str, t: types.Type) -> None:
        self.signals[symbol] = t
        self.variables[symbol] = t

    def add_variable(self, symbol: str, t: types.Type) -> None:
        self.variables[symbol] = t

    def add_definition(self, symbol: str, e: Expression) -> None:
        self.definitions[symbol] = e

    def add_struct(self, symbol: str, m: dict[str, types.Type]) -> None:
        self.structs[symbol] = m

    def add_atomic(self, symbol: str, e: Expression) -> None:
        self.atomic_checkers[symbol] = e

    def add_specification(self, symbol, s: Specification) -> None:
        self.specifications[symbol] = s

    def add_contract(self, symbol, c: Contract) -> None:
        self.contracts[symbol] = c

    def remove_variable(self, symbol) -> None:
        del self.variables[symbol]


def postorder(node: Node):
    """Yields C2PONodes in a postorder fashion starting from `node`."""
    stack: list[tuple[bool, Node]] = [(False, node)]
    visited: set[int] = set()

    while len(stack) > 0:
        cur = stack.pop()

        if cur[0]:
            yield cur[1]
            continue
        elif id(cur[1]) in visited:
            continue

        visited.add(id(cur[1]))
        stack.append((True, cur[1]))
        for child in reversed(cur[1].children):
            stack.append((False, child))


def preorder(node: Node):
    """Yields C2PONodes in a preorder fashion starting from `node`."""
    stack: list[Node] = [node]

    while len(stack) > 0:
        c = stack.pop()
        yield c

        for child in reversed(c.children):
            stack.append(child)


def rename(v: Node, repl: Node, expr: Node) -> Node:
    """Traverse expr and replace each node equal to v with repl."""
    # Special case: when expr is v
    if expr == v:
        return repl

    new: Node = deepcopy(expr)

    for node in postorder(new):
        if v == node:
            node.replace(repl)

    return new
