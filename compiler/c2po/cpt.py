"""C2PO Parse Tree (CPT) represents structure of a .c2po or .mltl file."""
from __future__ import annotations

import copy
import enum
import pickle
from typing import Iterator, Optional, Union, cast

from c2po import log, types

MODULE_CODE = "CPT"


class C2POSection(enum.Enum):
    STRUCT = 0
    INPUT = 1
    DEFINE = 2
    ATOMIC = 3
    FTSPEC = 4
    PTSPEC = 5


class Node:
    def __init__(self, loc: log.FileLocation) -> None:
        self.loc: log.FileLocation = loc
        self.symbol: str = ""

    def __str__(self) -> str:
        return self.symbol


class Expression(Node):
    def __init__(self, loc: log.FileLocation, children: list[Expression]) -> None:
        super().__init__(loc)
        self.engine = types.R2U2Engine.NONE
        self.atomic_id: int = -1  # only set for atomic propositions
        self.total_scq_size: int = -1
        self.scq_size: int = -1
        self.bpd: int = 0
        self.wpd: int = 0
        self.scq: tuple[int, int] = (-1, -1)
        self.type: types.Type = types.NoType()

        self.children: list[Expression] = []
        self.parents: list[Expression] = []

        for child in children:
            self.children.append(child)
            child.parents.append(self)

        self.replacement: Optional[Expression] = None

    def get_siblings(self) -> list[Expression]:
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

    def replace(self, new: Expression) -> None:
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

        self.replacement = new

    def copy_attrs(self, new: Expression) -> None:
        new.symbol = self.symbol
        new.scq_size = self.scq_size
        new.bpd = self.bpd
        new.wpd = self.wpd
        new.type = self.type

    def __deepcopy__(self, memo):
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(self.loc, children)
        self.copy_attrs(new)
        return new


class Literal(Expression):
    def __init__(self, loc: log.FileLocation) -> None:
        super().__init__(loc, [])

    def __str__(self) -> str:
        return self.symbol


class Constant(Literal):
    def __init__(self, loc: log.FileLocation, a: list[Node]) -> None:
        super().__init__(loc)
        self.value = 0

    def get_value(self) -> Union[int, float]:
        return self.value


class Bool(Constant):
    def __init__(self, loc: log.FileLocation, v: bool) -> None:
        super().__init__(loc, [])
        self.type = types.BoolType(True)
        self.bpd: int = 0
        self.wpd: int = 0
        self.value: bool = v
        self.symbol = str(v)
        self.engine = types.R2U2Engine.BOOLEANIZER


class Integer(Constant):
    def __init__(self, loc: log.FileLocation, v: int) -> None:
        super().__init__(loc, [])
        self.value: int = v
        self.symbol = str(v)
        self.type = types.IntType(True)
        self.engine = types.R2U2Engine.BOOLEANIZER

        if v.bit_length() > types.IntType.width:
            log.error(
                f"Constant '{v}' not representable in configured int width ('{types.IntType.width}').",
                module=MODULE_CODE,
                location=loc,
            )

    def get_value(self) -> int:
        return self.value

    def __deepcopy__(self, memo) -> Integer:
        new = Integer(self.loc, self.value)
        self.copy_attrs(new)
        return new


class Float(Constant):
    def __init__(self, loc: log.FileLocation, v: float) -> None:
        super().__init__(loc, [])
        self.type = types.FloatType(True)
        self.value: float = v
        self.symbol = str(v)
        self.engine = types.R2U2Engine.BOOLEANIZER

        # FIXME:
        # if len(v.hex()[2:]) > FLOAT.width:
        #     log.error(f"{ln} Constant '{v}' not representable in configured float width ('{FLOAT.width}').")

    def get_value(self) -> float:
        return self.value

    def __deepcopy__(self, memo) -> Float:
        new = Float(self.loc, self.value)
        self.copy_attrs(new)
        return new


class Variable(Expression):
    def __init__(self, loc: log.FileLocation, s: str) -> None:
        super().__init__(loc, [])
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
    def __init__(self, loc: log.FileLocation, s: str, t: types.Type) -> None:
        super().__init__(loc)
        self.symbol: str = s
        self.type: types.Type = t
        self.signal_id: int = -1
        self.engine = types.R2U2Engine.BOOLEANIZER

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Signal) and __o.symbol == self.symbol

    def __hash__(self) -> int:
        return id(self)

    def __deepcopy__(self, memo) -> Signal:
        copy = Signal(self.loc, self.symbol, self.type)
        return copy


class AtomicChecker(Literal):
    def __init__(self, loc: log.FileLocation, s: str) -> None:
        super().__init__(loc)
        self.symbol: str = s
        self.type: types.Type = types.BoolType(False)
        self.engine = types.R2U2Engine.ATOMIC_CHECKER

    def __deepcopy__(self, memo) -> AtomicChecker:
        copy = AtomicChecker(self.loc, self.symbol)
        self.copy_attrs(copy)
        return copy


class SetExpression(Expression):
    def __init__(self, loc: log.FileLocation, members: list[Expression]) -> None:
        super().__init__(loc, members)
        members.sort(key=lambda x: str(x))
        self.max_size: int = len(members)
        self.dynamic_size = None

    def set_dynamic_size(self, size: Node) -> None:
        self.dynamic_size = size

    def __str__(self) -> str:
        s: str = "{"
        for m in self.children:
            s += str(m) + ","
        s = s[:-1] + "}"
        return s


class Struct(Expression):
    def __init__(
        self, loc: log.FileLocation, s: str, m: dict[str, int], c: list[Expression]
    ) -> None:
        super().__init__(loc, c)
        self.symbol: str = s

        # hack to get named arguments -- see get_member
        # cannot use *just* members, else the parent tracking breaks
        self.members: dict[str, int] = m

    def get_member(self, name: str) -> Optional[Expression]:
        if name not in self.members:
            log.internal(
                f"Member '{name}' not in members of '{self.symbol}'",
                module=MODULE_CODE,
                location=self.loc,
            )
            return None

        member = self.children[self.members[name]]

        if member is None:
            log.internal(
                f"Member '{name}' not in members of '{self.symbol}'",
                module=MODULE_CODE,
                location=self.loc,
            )
            return None

        return cast(Expression, member)

    def __deepcopy__(self, memo) -> Struct:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = Struct(self.loc, self.symbol, self.members, children)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s = self.symbol + "("
        s += ",".join([f"{i}={self.children[e]}" for i, e in self.members.items()])
        s += ")"
        return s


class StructAccess(Expression):
    def __init__(self, loc: log.FileLocation, struct: Expression, member: str) -> None:
        super().__init__(loc, [struct])
        self.member: str = member

    def get_struct(self) -> Struct:
        return cast(Struct, self.children[0])

    def __deepcopy__(self, memo) -> StructAccess:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(self.loc, children[0], self.member)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return str(self.get_struct()) + "." + self.member


class Operator(Expression):
    def __init__(self, loc: log.FileLocation, children: list[Expression]) -> None:
        super().__init__(loc, children)
        self.arity: int = len(children)

    def get_operand(self, i: int) -> Expression:
        return cast(Expression, self.children[i])


class FunctionCall(Operator):
    def __init__(self, loc: log.FileLocation, s: str, a: list[Expression]) -> None:
        super().__init__(loc, a)
        self.symbol: str = s

    def __deepcopy__(self, memo) -> FunctionCall:
        return FunctionCall(
            self.loc,
            self.symbol,
            copy.deepcopy(cast("list[Expression]", self.children), memo),
        )

    def __str__(self) -> str:
        s = f"{self.symbol}("
        for arg in self.children:
            s += f"{arg},"
        return s[:-1] + ")"


class Bind(Expression):
    def __init__(
        self, loc: log.FileLocation, var: Variable, set: SetExpression
    ) -> None:
        super().__init__(loc, [])
        self.bound_var = var
        self.set_expr = set

    def get_bound_var(self) -> Variable:
        return self.bound_var

    def get_set(self) -> SetExpression:
        return self.set_expr

    def __str__(self) -> str:
        return ""


class SetAggregation(Operator):
    """`SetAggOperator` tree structure looks like:

    SetAggOperator
    ____|___________
    |   |     |    |
    v   v     v    v
    Set [Num] Bind Expression

    where from the left we have the target set, (optional) number, a dummy class to do variable binding during traversal, then the argument expression. We visit these in that order when performing the standard reverse postorder traversal.
    """

    def __init__(
        self,
        loc: log.FileLocation,
        var: Variable,
        set: SetExpression,
        num: Optional[Expression],
        expr: Expression,
    ) -> None:
        if num:
            super().__init__(loc, [set, num, Bind(loc, var, set), expr])
        else:
            super().__init__(loc, [set, Bind(loc, var, set), expr])
        self.bound_var = var

    def get_set(self) -> SetExpression:
        return cast(SetExpression, self.children[0])

    def get_expr(self) -> Expression:
        """Returns the aggregated `Expression`. This is always the last child, see docstring of `SetAggregation` for a visual."""
        return cast(Expression, self.children[-1])

    def __str__(self) -> str:
        return (
            self.symbol
            + "("
            + str(self.bound_var)
            + ":"
            + str(self.get_set())
            + ")"
            + "("
            + str(self.get_expr())
            + ")"
        )


class ForEach(SetAggregation):
    def __init__(
        self, loc: log.FileLocation, var: Variable, set: SetExpression, expr: Expression
    ) -> None:
        super().__init__(loc, var, set, None, expr)
        self.symbol: str = "foreach"

    def __deepcopy__(self, memo) -> SetAggregation:
        # assumes that __deepcopy__ is implemented by all sub-classes where num is not None
        new = ForEach(
            self.loc,
            cast(Variable, copy.deepcopy(self.bound_var)),
            cast(SetExpression, copy.deepcopy(self.children[0])),
            copy.deepcopy(self.children[-1]),
        )
        self.copy_attrs(new)
        return new


class ForSome(SetAggregation):
    def __init__(
        self, loc: log.FileLocation, var: Variable, set: SetExpression, expr: Expression
    ) -> None:
        super().__init__(loc, var, set, None, expr)
        self.symbol: str = "forsome"

    def __deepcopy__(self, memo) -> SetAggregation:
        # assumes that __deepcopy__ is implemented by all sub-classes where num is not None
        new = ForSome(
            self.loc,
            cast(Variable, copy.deepcopy(self.bound_var, memo)),
            cast(SetExpression, copy.deepcopy(self.children[0], memo)),
            copy.deepcopy(self.children[-1], memo),
        )
        self.copy_attrs(new)
        return new


class ForExactly(SetAggregation):
    def __init__(
        self,
        loc: log.FileLocation,
        var: Variable,
        set: SetExpression,
        num: Expression,
        expr: Expression,
    ) -> None:
        super().__init__(loc, var, set, num, expr)
        self.symbol: str = "forexactly"

    def get_num(self) -> Expression:
        return cast(Expression, self.children[1])

    def __deepcopy__(self, memo) -> ForExactly:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ForExactly(
            self.loc,
            self.bound_var,
            cast(SetExpression, children[0]),
            children[1],
            cast(Expression, children[:-1]),
        )
        self.copy_attrs(new)
        return new


class ForAtLeast(SetAggregation):
    def __init__(
        self,
        loc: log.FileLocation,
        var: Variable,
        set: SetExpression,
        num: Expression,
        expr: Expression,
    ) -> None:
        super().__init__(loc, var, set, num, expr)
        self.symbol: str = "foratleast"

    def get_num(self) -> Expression:
        return cast(Expression, self.children[1])

    def __deepcopy__(self, memo) -> ForAtLeast:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ForAtLeast(
            self.loc,
            cast(Variable, children[1]),
            cast(SetExpression, children[0]),
            children[2],
            cast(Expression, children[:-1]),
        )
        self.copy_attrs(new)
        return new


class ForAtMost(SetAggregation):
    def __init__(
        self,
        loc: log.FileLocation,
        var: Variable,
        set: SetExpression,
        num: Expression,
        expr: Expression,
    ) -> None:
        super().__init__(loc, var, set, num, expr)
        self.symbol: str = "foratmost"

    def get_num(self) -> Expression:
        return cast(Expression, self.children[1])

    def __deepcopy__(self, memo) -> ForAtMost:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ForAtMost(
            self.loc,
            cast(Variable, children[1]),
            cast(SetExpression, children[0]),
            children[2],
            cast(Expression, children[:-1]),
        )
        self.copy_attrs(new)
        return new


class Count(Operator):
    def __init__(
        self, loc: log.FileLocation, num: Expression, children: list[Expression]
    ) -> None:
        # Note: all members of c must be of type Boolean
        super().__init__(loc, [num] + children)
        self.name = "count"

    def __deepcopy__(self, memo) -> Count:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = Count(self.loc, cast(Expression, children[0]), children[1:])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s = "count("
        for c in self.children:
            s += str(c) + ","
        return s[:-1] + ")"


class BitwiseOperator(Operator):
    def __init__(self, loc: log.FileLocation, operands: list[Expression]) -> None:
        super().__init__(loc, operands)
        self.engine = types.R2U2Engine.BOOLEANIZER


class BitwiseAnd(BitwiseOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "&"

    def __deepcopy__(self, memo) -> BitwiseAnd:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = BitwiseAnd(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseOr(BitwiseOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "|"

    def __deepcopy__(self, memo) -> BitwiseOr:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = BitwiseOr(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseXor(BitwiseOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "^"

    def __deepcopy__(self, memo) -> BitwiseXor:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = BitwiseXor(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseShiftLeft(BitwiseOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "<<"

    def __deepcopy__(self, memo) -> BitwiseShiftLeft:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = BitwiseShiftLeft(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseShiftRight(BitwiseOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = ">>"

    def __deepcopy__(self, memo) -> BitwiseShiftRight:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = BitwiseShiftRight(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class BitwiseNegate(BitwiseOperator):
    def __init__(self, loc: log.FileLocation, operand: Expression) -> None:
        super().__init__(loc, [operand])
        self.symbol = "~"

    def __deepcopy__(self, memo) -> BitwiseNegate:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = BitwiseNegate(self.loc, children[0])
        self.copy_attrs(new)
        return new


class ArithmeticOperator(Operator):
    def __init__(self, loc: log.FileLocation, operands: list[Expression]) -> None:
        super().__init__(loc, operands)
        self.engine = types.R2U2Engine.BOOLEANIZER

    def __str__(self) -> str:
        s = f"{self.children[0]}"
        for c in range(1, len(self.children)):
            s += f"{self.symbol}{self.children[c]}"
        return s


class ArithmeticAdd(ArithmeticOperator):
    def __init__(self, loc: log.FileLocation, operands: list[Expression]) -> None:
        # force binary operator for now
        if len(operands) > 2:
            prev = ArithmeticAdd(loc, operands[0:2])
            for i in range(2, len(operands) - 1):
                prev = ArithmeticAdd(loc, [prev, operands[i]])
            super().__init__(loc, [prev, operands[len(operands) - 1]])
            self.type = self.get_operand(0).type
        else:
            super().__init__(loc, operands)
            self.type = self.get_operand(0).type

        self.symbol = "+"

    def __deepcopy__(self, memo) -> ArithmeticAdd:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ArithmeticAdd(self.loc, children)
        self.copy_attrs(new)
        return new


class ArithmeticSubtract(ArithmeticOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "-"

    def __deepcopy__(self, memo) -> ArithmeticSubtract:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ArithmeticSubtract(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticMultiply(ArithmeticOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "*"

    def __deepcopy__(self, memo) -> ArithmeticMultiply:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ArithmeticMultiply(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticDivide(ArithmeticOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "/"

    def __deepcopy__(self, memo) -> ArithmeticDivide:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ArithmeticDivide(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticModulo(ArithmeticOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "%"

    def __deepcopy__(self, memo) -> ArithmeticModulo:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ArithmeticModulo(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class ArithmeticNegate(ArithmeticOperator):
    def __init__(self, loc: log.FileLocation, operand: Expression) -> None:
        super().__init__(loc, [operand])
        self.symbol = "-"

    def __deepcopy__(self, memo) -> ArithmeticNegate:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ArithmeticNegate(self.loc, children[0])
        self.copy_attrs(new)
        return new


class RelationalOperator(Operator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.engine = types.R2U2Engine.BOOLEANIZER

    def __deepcopy__(self, memo) -> RelationalOperator:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.children[0]}){self.symbol}({self.children[1]})"


class Equal(RelationalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, lhs, rhs)
        self.symbol = "=="


class NotEqual(RelationalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, lhs, rhs)
        self.symbol = "!="


class GreaterThan(RelationalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, lhs, rhs)
        self.symbol = ">"


class LessThan(RelationalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, lhs, rhs)
        self.symbol = "<"


class GreaterThanOrEqual(RelationalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, lhs, rhs)
        self.symbol = ">="


class LessThanOrEqual(RelationalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, lhs, rhs)
        self.symbol = "<="


class LogicalOperator(Operator):
    def __init__(self, loc: log.FileLocation, operands: list[Expression]) -> None:
        super().__init__(loc, operands)
        self.bpd = min([child.bpd for child in self.children])
        self.wpd = max([child.wpd for child in self.children])
        self.engine = types.R2U2Engine.TEMPORAL_LOGIC


class LogicalOr(LogicalOperator):
    def __init__(self, loc: log.FileLocation, operands: list[Expression]) -> None:
        # force binary operator for now
        if len(operands) > 2:
            prev = LogicalOr(loc, operands[0:2])
            for i in range(2, len(operands) - 1):
                prev = LogicalOr(loc, [prev, operands[i]])
            super().__init__(loc, [prev, operands[len(operands) - 1]])
        else:
            super().__init__(loc, operands)

        super().__init__(loc, operands)
        self.symbol = "||"

    def __str__(self) -> str:
        return self.symbol.join([str(c) for c in self.children])


class LogicalAnd(LogicalOperator):
    def __init__(self, loc: log.FileLocation, operands: list[Expression]) -> None:
        # force binary operator for now
        if len(operands) > 2:
            prev = LogicalAnd(loc, operands[0:2])
            for i in range(2, len(operands) - 1):
                prev = LogicalAnd(loc, [prev, operands[i]])
            super().__init__(loc, [prev, operands[len(operands) - 1]])
        else:
            super().__init__(loc, operands)

        self.symbol = "&&"

    def __str__(self) -> str:
        return self.symbol.join([str(c) for c in self.children])


class LogicalXor(LogicalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "^^"

    def __deepcopy__(self, memo) -> LogicalXor:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = LogicalXor(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class LogicalImplies(LogicalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "->"

    def __deepcopy__(self, memo) -> LogicalImplies:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = LogicalImplies(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class LogicalIff(LogicalOperator):
    def __init__(self, loc: log.FileLocation, lhs: Expression, rhs: Expression) -> None:
        super().__init__(loc, [lhs, rhs])
        self.symbol = "<->"

    def __deepcopy__(self, memo) -> LogicalIff:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = LogicalIff(self.loc, children[0], children[1])
        self.copy_attrs(new)
        return new


class LogicalNegate(LogicalOperator):
    def __init__(self, loc: log.FileLocation, operand: Expression) -> None:
        super().__init__(loc, [operand])
        self.symbol = "!"

    def __deepcopy__(self, memo) -> LogicalNegate:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = LogicalNegate(self.loc, children[0])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"!({self.children[0]})"


class TemporalOperator(Operator):
    def __init__(
        self, loc: log.FileLocation, operands: list[Expression], lb: int, ub: int
    ) -> None:
        super().__init__(loc, operands)
        self.interval = types.Interval(lb=lb, ub=ub)
        self.engine = types.R2U2Engine.TEMPORAL_LOGIC


class FutureTimeOperator(TemporalOperator):
    def __init__(
        self, loc: log.FileLocation, operands: list[Expression], lb: int, ub: int
    ) -> None:
        super().__init__(loc, operands, lb, ub)


class PastTimeOperator(TemporalOperator):
    def __init__(
        self, loc: log.FileLocation, operands: list[Expression], lb: int, ub: int
    ) -> None:
        super().__init__(loc, operands, lb, ub)


class FutureTimeBinaryOperator(TemporalOperator):
    def __init__(
        self, loc: log.FileLocation, lhs: Expression, rhs: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, [lhs, rhs], lb, ub)
        self.bpd = min(self.children[0].bpd, self.children[1].bpd) + self.interval.lb
        self.wpd = max(self.children[0].wpd, self.children[1].wpd) + self.interval.ub

    def get_lhs(self) -> Expression:
        return self.get_operand(0)

    def get_rhs(self) -> Expression:
        return self.get_operand(1)

    def __deepcopy__(self, memo) -> FutureTimeBinaryOperator:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(
            self.loc, children[0], children[1], self.interval.lb, self.interval.ub
        )
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.children[0]!s}){self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})"


class Until(FutureTimeBinaryOperator):
    def __init__(
        self, loc: log.FileLocation, lhs: Expression, rhs: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, lhs, rhs, lb, ub)
        self.symbol = "U"


class Release(FutureTimeBinaryOperator):
    def __init__(
        self, loc: log.FileLocation, lhs: Expression, rhs: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, lhs, rhs, lb, ub)
        self.symbol = "R"


class FutureTimeUnaryOperator(FutureTimeOperator):
    def __init__(
        self, loc: log.FileLocation, operand: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, [operand], lb, ub)
        self.bpd = self.get_operand().bpd + self.interval.lb
        self.wpd = self.get_operand().wpd + self.interval.ub

    def get_operand(self) -> Expression:
        return cast(Expression, self.children[0])

    def __deepcopy__(self, memo) -> FutureTimeUnaryOperator:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(self.loc, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"


class Global(FutureTimeUnaryOperator):
    def __init__(
        self, loc: log.FileLocation, operand: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, operand, lb, ub)
        self.symbol = "G"


class Future(FutureTimeUnaryOperator):
    def __init__(
        self, loc: log.FileLocation, operands: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, operands, lb, ub)
        self.symbol = "F"


class PastTimeBinaryOperator(PastTimeOperator):
    def __init__(
        self, loc: log.FileLocation, lhs: Expression, rhs: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, [lhs, rhs], lb, ub)

    def get_lhs(self) -> Expression:
        return self.get_operand(0)

    def get_rhs(self) -> Expression:
        return self.get_operand(1)

    def __deepcopy__(self, memo) -> PastTimeBinaryOperator:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(
            self.loc, children[0], children[1], self.interval.lb, self.interval.ub
        )
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.children[0]!s}){self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.children[1]!s})"


class Since(PastTimeBinaryOperator):
    def __init__(
        self, loc: log.FileLocation, lhs: Expression, rhs: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, lhs, rhs, lb, ub)
        self.symbol = "S"


class PastTimeUnaryOperator(PastTimeOperator):
    def __init__(
        self, loc: log.FileLocation, operand: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, [operand], lb, ub)

    def get_operand(self) -> Expression:
        return cast(Expression, self.children[0])

    def __deepcopy__(self, memo) -> PastTimeUnaryOperator:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(self.loc, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"


class Historical(PastTimeUnaryOperator):
    def __init__(
        self, loc: log.FileLocation, operand: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, operand, lb, ub)
        self.symbol = "H"


class Once(PastTimeUnaryOperator):
    def __init__(
        self, loc: log.FileLocation, operand: Expression, lb: int, ub: int
    ) -> None:
        super().__init__(loc, operand, lb, ub)
        self.symbol = "O"


class Formula(Expression):
    def __init__(
        self, loc: log.FileLocation, label: str, fnum: int, expr: Expression
    ) -> None:
        super().__init__(loc, [expr])
        self.symbol: str = label
        self.formula_number: int = fnum
        self.engine = types.R2U2Engine.TEMPORAL_LOGIC

    def get_expr(self) -> Expression:
        return cast(Expression, self.children[0])

    def __deepcopy__(self, memo) -> Formula:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = Formula(self.loc, self.symbol, self.formula_number, children[0])
        self.copy_attrs(new)
        return new
    
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, Formula) and self.symbol == __value.symbol
    
    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        return (
            (str(self.formula_number) if self.symbol[0] == "#" else self.symbol)
            + ": "
            + str(self.get_expr())
        )


class Contract(Expression):
    def __init__(
        self,
        loc: log.FileLocation,
        label: str,
        fnum1: int,
        fnum2: int,
        fnum3: int,
        assume: Expression,
        guarantee: Expression,
    ) -> None:
        super().__init__(loc, [assume, guarantee])
        self.symbol: str = label
        self.formula_numbers: tuple[int, int, int] = (fnum1, fnum2, fnum3)

    def get_assumption(self) -> Expression:
        return self.children[0]

    def get_guarantee(self) -> Expression:
        return self.children[1]
    
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, Contract) and self.symbol == __value.symbol
    
    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        return f"{self.symbol}: ({self.get_assumption()})=>({self.get_guarantee()})"


Specification = Union[Formula, Contract]


class SpecificationSet(Expression):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc, cast("list[Expression]", specs))

    def get_specs(self) -> list[Specification]:
        return cast("list[Specification]", self.children)


class StructDefinition(Node):
    def __init__(
        self, loc: log.FileLocation, symbol: str, var_decls: list[VariableDeclaration]
    ) -> None:
        super().__init__(loc)
        self.symbol = symbol
        self.var_decls = var_decls
        self.members = {}
        for var_decl in var_decls:
            for sym in var_decl.variables:
                self.members[sym] = var_decl.type

    def __str__(self) -> str:
        members_str_list = [str(s) + ";" for s in self.var_decls]
        return self.symbol + "{" + " ".join(members_str_list) + ")"


class VariableDeclaration(Node):
    def __init__(self, loc: log.FileLocation, vars: list[str], t: types.Type) -> None:
        super().__init__(loc)
        self.variables = vars
        self.type = t

    def __str__(self) -> str:
        return f"{','.join(self.variables)}: {str(self.type)}"


class Definition(Node):
    def __init__(self, loc: log.FileLocation, symbol: str, expr: Expression) -> None:
        super().__init__(loc)
        self.symbol = symbol
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.symbol} := {self.expr}"


class AtomicCheckerDefinition(Node):
    def __init__(self, loc: log.FileLocation, symbol: str, expr: Expression) -> None:
        super().__init__(loc)
        self.symbol = symbol
        self.expr = expr

    def get_expr(self) -> Expression:
        return cast(Expression, self.expr)

    def __str__(self) -> str:
        return f"{self.symbol} := {self.get_expr()}"


class StructSection(Node):
    def __init__(
        self, loc: log.FileLocation, struct_defs: list[StructDefinition]
    ) -> None:
        super().__init__(loc)
        self.struct_defs = struct_defs

    def __str__(self) -> str:
        structs_str_list = [str(s) + ";" for s in self.struct_defs]
        return "STRUCT\n\t" + "\n\t".join(structs_str_list)


class InputSection(Node):
    def __init__(
        self, loc: log.FileLocation, signal_decls: list[VariableDeclaration]
    ) -> None:
        super().__init__(loc)
        self.signal_decls = signal_decls

    def __str__(self) -> str:
        signals_str_list = [str(s) + ";" for s in self.signal_decls]
        return "INPUT\n\t" + "\n\t".join(signals_str_list)


class DefineSection(Node):
    def __init__(self, loc: log.FileLocation, defines: list[Definition]) -> None:
        super().__init__(loc)
        self.defines = defines

    def __str__(self) -> str:
        defines_str_list = [str(s) + ";" for s in self.defines]
        return "DEFINE\n\t" + "\n\t".join(defines_str_list)


class AtomicSection(Node):
    def __init__(self, loc: log.FileLocation, atomics: list[AtomicCheckerDefinition]):
        super().__init__(loc)
        self.atomics = atomics

    def __str__(self) -> str:
        atomics_str_list = [str(s) + ";" for s in self.atomics]
        return "ATOMIC\n\t" + "\n\t".join(atomics_str_list)


class SpecSection(Node):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc)
        self.specs = specs


class FutureTimeSpecSection(SpecSection):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc, specs)

    def __str__(self) -> str:
        return "FTPSEC\n\t" + "\n\t".join([str(spec) for spec in self.specs])


class PastTimeSpecSection(SpecSection):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc, specs)

    def __str__(self) -> str:
        return "PTSPEC\n\t" + "\n\t".join([str(spec) for spec in self.specs])


ProgramSection = Union[
    StructSection, InputSection, DefineSection, AtomicSection, SpecSection
]


class Program(Node):
    def __init__(self, loc: log.FileLocation, sections: list[ProgramSection]) -> None:
        super().__init__(loc)
        self.sections = sections

        ft_specs: list[Specification] = []
        pt_specs: list[Specification] = []
        for section in sections:
            if isinstance(section, FutureTimeSpecSection):
                ft_specs += section.specs
            elif isinstance(section, PastTimeSpecSection):
                pt_specs += section.specs

        self.ft_spec_set = SpecificationSet(loc, ft_specs)
        self.pt_spec_set = SpecificationSet(loc, pt_specs)

    def replace_spec(self, spec: Specification, new: list[Specification]) -> None:
        """Replaces `spec` with `new` in this `Program`, if `spec` is present. Raises `KeyError` if `spec` is not present."""
        try:
            index = self.ft_spec_set.children.index(spec)
            self.ft_spec_set.children[index:index+1] = new
        except IndexError:
            index = self.pt_spec_set.children.index(spec)
            self.pt_spec_set.children[index:index+1] = new

    def get_specs(self) -> list[Specification]:
        return self.ft_spec_set.get_specs() + self.pt_spec_set.get_specs()

    def postorder(self, context: Context):
        """Performs a postorder traversal of each FT and PT specification in this `Program`."""
        for expr in postorder(self.ft_spec_set, context):
            yield expr

        for expr in postorder(self.pt_spec_set, context):
            yield expr

    def preorder(self, context: Context):
        """Performs a preorder traversal of each FT and PT specification in this `Program`."""
        for expr in preorder(self.ft_spec_set, context):
            yield expr

        for expr in preorder(self.pt_spec_set, context):
            yield expr

    def pickle(self) -> bytes:
        return pickle.dumps(self)

    def __str__(self) -> str:
        return "\n".join([str(s) for s in self.sections])


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
        self.specifications: dict[str, Formula] = {}
        self.contracts: dict[str, Contract] = {}
        self.atomics: set[Expression] = set()
        self.implementation = impl
        self.booleanizer_enabled = booleanizer
        self.atomic_checker_enabled = atomic_checkers
        self.mission_time = mission_time
        self.signal_mapping = signal_mapping
        self.assembly_enabled = assembly_enabled
        self.bound_vars: dict[str, SetExpression] = {}

        self.is_ft = False
        self.has_future_time = False
        self.has_past_time = False

    def get_symbols(self) -> list[str]:
        symbols = [s for s in self.definitions.keys()]
        symbols += [s for s in self.structs.keys()]
        symbols += [s for s in self.signals.keys()]
        symbols += [s for s in self.variables.keys()]
        symbols += [s for s in self.atomic_checkers.keys()]
        symbols += [s for s in self.specifications.keys()]
        symbols += [s for s in self.contracts.keys()]
        symbols += [s for s in self.bound_vars.keys()]
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

    def add_formula(self, symbol, s: Formula) -> None:
        self.specifications[symbol] = s

    def add_contract(self, symbol, c: Contract) -> None:
        self.contracts[symbol] = c

    def remove_variable(self, symbol) -> None:
        del self.variables[symbol]


def postorder(
    start: Union[Expression, list[Expression]], context: Context
) -> Iterator[Expression]:
    """Performs a postorder traversal of `start`. If `start` is a list of `Expression`s, then initializes the stack to `start`. Uses `context` to handle local context (for example, variable binding in set aggregation expressions)."""
    stack: list[tuple[bool, Expression]] = []
    visited: set[int] = set()

    if isinstance(start, Expression):
        stack.append((False, start))
    else:
        [stack.append((False, expr)) for expr in start]

    while len(stack) > 0:
        (seen, expr) = stack.pop()

        if seen and isinstance(expr, SetAggregation):
            del context.bound_vars[expr.bound_var.symbol]
            yield expr
            continue
        elif seen and isinstance(expr, Bind):
            context.bound_vars[expr.bound_var.symbol] = expr.get_set()
            continue
        elif seen:
            yield expr
            continue
        elif id(expr) in visited:
            continue

        visited.add(id(expr))
        stack.append((True, expr))

        for child in reversed(expr.children):
            stack.append((False, child))


def preorder(
    start: Union[Expression, list[Expression]], context: Context
) -> Iterator[Expression]:
    """Performs a preorder traversal of `start`. If `start` is a list of `Expression`s, then initializes the stack to `start`. Uses `context` to handle local context (for example, variable binding in set aggregation expressions)."""
    stack: list[Expression] = []
    visited: set[int] = set()

    if isinstance(start, Expression):
        stack.append(start)
    else:
        [stack.append(expr) for expr in start]

    while len(stack) > 0:
        expr = stack.pop()

        if id(expr) in visited:
            continue

        yield expr

        # if expr has been replaced since we just yielded it, need to traverse down the replacement node
        cur = expr.replacement if expr.replacement else expr

        visited.add(id(cur))

        for child in reversed(cur.children):
            stack.append(child)


def rename(
    target: Expression, repl: Expression, expr: Expression, context: Context
) -> Expression:
    """Traverse `expr` and replace each node equal to `target` with `repl`."""
    # Special case: when expr is target
    if expr == target:
        return repl

    new: Node = copy.deepcopy(expr)

    for node in postorder(new, context):
        if target == node:
            node.replace(repl)

    return new
