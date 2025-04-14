"""C2PO Parse Tree (CPT) represents structure of a .c2po or .mltl file."""

from __future__ import annotations

import copy
import enum
import pickle
from typing import Iterator, Optional, Union, cast, Any

from c2po import log, types, options

MODULE_CODE = "CPT"


class C2POSection(enum.Enum):
    STRUCT = 0
    INPUT = 1
    DEFINE = 2
    FTSPEC = 3
    PTSPEC = 4


class CompilationStage(enum.Enum):
    PARSE = 0
    TYPE_CHECK = 1
    PASSES = 2
    ASSEMBLE = 3


class Node:
    def __init__(self, loc: log.FileLocation) -> None:
        self.loc: log.FileLocation = loc
        self.symbol: str = ""

    def __str__(self) -> str:
        return self.symbol


class Expression(Node):
    def __init__(
        self,
        loc: log.FileLocation,
        children: list[Expression],
        type: types.Type = types.NoType(),
    ) -> None:
        super().__init__(loc)
        self.engine = types.R2U2Engine.NONE
        self.total_scq_size: int = -1
        self.scq_size: int = -1
        self.bpd: int = 0
        self.wpd: int = 0
        self.scq: tuple[int, int] = (-1, -1)
        self.type: types.Type = type

        self.children: list[Expression] = []
        self.parents: list[Expression] = []

        for child in children:
            self.children.append(child)
            child.parents.append(self)

        # Used for pre-order traversal, if this has been replaced during traversal
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
    
    def get_descendants(self) -> list[Expression]:
        prev_visited_children: list[Expression] = [self]
        visited_children: list[Expression] = []
        children: list[Expression] = []
        while(True):  
            for node in prev_visited_children:
                for child in node.children:
                    if not isinstance(child, SpecificationSet):
                        visited_children.append(child)
                        children.append(child)
            if(len(visited_children) == 0):
                return children
            prev_visited_children = visited_children
            visited_children = []
   


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

    def has_only_tl_parents(self) -> bool:
        """Returns True if all parents of this node are computed by the TL Engine (is a logical or temporal operator)."""
        return all(
            [
                parent.engine is types.R2U2Engine.TEMPORAL_LOGIC
                for parent in self.parents
            ]
        )

    def copy_attrs(self, new: Expression) -> None:
        new.symbol = self.symbol
        new.engine = self.engine
        new.scq_size = self.scq_size
        new.total_scq_size = self.total_scq_size
        new.bpd = self.bpd
        new.wpd = self.wpd
        new.scq = self.scq
        new.type = self.type

    def __str__(self) -> str:
        return to_infix_str(self)

    def __repr__(self) -> str:
        return to_prefix_str(self)


class Constant(Expression):
    def __init__(self, loc: log.FileLocation, value: Any) -> None:
        super().__init__(loc, [])
        self.value: bool = value
        self.symbol = str(value)
        self.engine = types.R2U2Engine.BOOLEANIZER

        if isinstance(value, bool):
            self.type = types.BoolType(True)
        elif isinstance(value, int):
            self.type = types.IntType(True)
        elif isinstance(value, float):
            self.type = types.FloatType(True)
        else:
            raise ValueError(f"Bad value ({value})")

    def __deepcopy__(self, memo):
        new = Constant(self.loc, self.value)
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

    def __deepcopy__(self, memo):
        new = Variable(self.loc, self.symbol)
        self.copy_attrs(new)
        return new


class Signal(Expression):
    def __init__(self, loc: log.FileLocation, s: str, t: types.Type) -> None:
        super().__init__(loc, [])
        self.symbol: str = s
        self.type: types.Type = t
        self.signal_id: int = -1

    def __deepcopy__(self, memo) -> Signal:
        new = Signal(self.loc, self.symbol, self.type)
        self.copy_attrs(new)
        new.signal_id = self.signal_id
        return new


class ArrayExpression(Expression):
    def __init__(self, loc: log.FileLocation, members: list[Expression]) -> None:
        super().__init__(loc, members)
        self.max_size: int = len(members)

    def __deepcopy__(self, memo):
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = ArrayExpression(self.loc, children)
        self.copy_attrs(new)
        return new


class ArrayIndex(Expression):
    def __init__(self, loc: log.FileLocation, array: Expression, index: int) -> None:
        super().__init__(loc, [array])
        self.index = index
        self.symbol = "[]"

    def get_array(self) -> Expression:
        return self.children[0]

    def get_index(self) -> int:
        return self.index

    def __deepcopy__(self, memo) -> ArrayIndex:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(self.loc, children[0], self.index)
        self.copy_attrs(new)
        return new


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
                MODULE_CODE,
                f"Member '{name}' not in members of '{self.symbol}'",
                self.loc,
            )
            return None

        member = self.children[self.members[name]]

        if member is None:
            log.internal(
                MODULE_CODE,
                f"Member '{name}' not in members of '{self.symbol}'",
                self.loc,
            )
            return None

        return cast(Expression, member)

    def __deepcopy__(self, memo) -> Struct:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = Struct(self.loc, self.symbol, self.members, children)
        self.copy_attrs(new)
        return new


class StructAccess(Expression):
    def __init__(self, loc: log.FileLocation, struct: Expression, member: str) -> None:
        super().__init__(loc, [struct])
        self.member: str = member
        self.symbol = "."

    def get_struct(self) -> Struct:
        return cast(Struct, self.children[0])

    def __deepcopy__(self, memo) -> StructAccess:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = type(self)(self.loc, children[0], self.member)
        self.copy_attrs(new)
        return new


class FunctionCall(Expression):
    def __init__(
        self, loc: log.FileLocation, s: str, operands: list[Expression]
    ) -> None:
        super().__init__(loc, operands)
        self.symbol: str = s

    def __deepcopy__(self, memo) -> FunctionCall:
        return FunctionCall(
            self.loc,
            self.symbol,
            copy.deepcopy(cast("list[Expression]", self.children), memo),
        )


class Bind(Expression):
    """Dummy class used for traversal of set aggregation operators. See constructor for the operators in the `Operator` class."""

    def __init__(
        self, loc: log.FileLocation, var: Variable, set: ArrayExpression
    ) -> None:
        super().__init__(loc, [])
        self.bound_var = var
        self.set_expr = set

    def get_bound_var(self) -> Variable:
        return self.bound_var

    def get_set(self) -> ArrayExpression:
        return self.set_expr

    def __str__(self) -> str:
        return ""

    def __deepcopy__(self, memo):
        new = Bind(self.loc, self.bound_var, self.set_expr)
        self.copy_attrs(new)
        return new


class SetAggregationKind(enum.Enum):
    FOR_EACH = "foreach"
    FOR_SOME = "forsome"
    FOR_EXACTLY = "forexactly"
    FOR_AT_LEAST = "foratleast"
    FOR_AT_MOST = "foratmost"


class SetAggregation(Expression):
    """`SetAggregation` tree structure looks like:

    SetAggregation
    ____|___________
    |   |     |    |
    v   v     v    v
    Set [Num] Bind Expression

    where from the left we have the target set, (optional) number, a dummy class to do variable binding during traversal, then the argument expression. We visit these in that order when performing the standard reverse postorder traversal.
    """

    def __init__(
        self,
        loc: log.FileLocation,
        operator: SetAggregationKind,
        var: Variable,
        set: ArrayExpression,
        num: Optional[Expression],
        expr: Expression,
    ) -> None:
        if num:
            super().__init__(loc, [set, num, Bind(loc, var, set), expr])
        else:
            super().__init__(loc, [set, Bind(loc, var, set), expr])

        self.operator = operator
        self.bound_var = var

    @staticmethod
    def ForEach(
        loc: log.FileLocation, var: Variable, set: ArrayExpression, expr: Expression
    ) -> SetAggregation:
        return SetAggregation(loc, SetAggregationKind.FOR_EACH, var, set, None, expr)

    @staticmethod
    def ForSome(
        loc: log.FileLocation, var: Variable, set: ArrayExpression, expr: Expression
    ) -> SetAggregation:
        return SetAggregation(loc, SetAggregationKind.FOR_SOME, var, set, None, expr)

    @staticmethod
    def ForExactly(
        loc: log.FileLocation,
        var: Variable,
        set: ArrayExpression,
        num: Expression,
        expr: Expression,
    ) -> SetAggregation:
        return SetAggregation(loc, SetAggregationKind.FOR_EXACTLY, var, set, num, expr)

    @staticmethod
    def ForAtMost(
        loc: log.FileLocation,
        var: Variable,
        set: ArrayExpression,
        num: Expression,
        expr: Expression,
    ) -> SetAggregation:
        return SetAggregation(loc, SetAggregationKind.FOR_AT_MOST, var, set, num, expr)

    @staticmethod
    def ForAtLeast(
        loc: log.FileLocation,
        var: Variable,
        set: ArrayExpression,
        num: Expression,
        expr: Expression,
    ) -> SetAggregation:
        return SetAggregation(loc, SetAggregationKind.FOR_AT_LEAST, var, set, num, expr)

    def get_num(self) -> Expression:
        if len(self.children) < 4:
            raise ValueError(
                f"Attempting to access num for set agg operator that does not have one ({self})"
            )
        return self.children[1]

    def get_set(self) -> ArrayExpression:
        return cast(ArrayExpression, self.children[0])

    def get_expr(self) -> Expression:
        """Returns the aggregated `Expression`. This is always the last child, see docstring of `SetAggregation` for a visual."""
        return cast(Expression, self.children[-1])

    def __deepcopy__(self, memo):
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = SetAggregation(
            self.loc,
            self.operator,
            cast(Variable, copy.deepcopy(self.bound_var, memo)),
            cast(ArrayExpression, children[0]),
            children[1] if len(self.children) == 4 else None,
            cast(Expression, children[-1]),
        )
        self.copy_attrs(new)
        return new


class OperatorKind(enum.Enum):
    # Bitwise
    BITWISE_AND = "&"
    BITWISE_OR = "|"
    BITWISE_XOR = "^"
    BITWISE_NEGATE = "~"
    SHIFT_LEFT = "<<"
    SHIFT_RIGHT = ">>"

    # Arithmetic
    ARITHMETIC_ADD = "+"
    ARITHMETIC_SUBTRACT = "-"
    ARITHMETIC_MULTPLY = "*"
    ARITHMETIC_DIVIDE = "/"
    ARITHMETIC_MODULO = "%"
    ARITHMETIC_NEGATE = "-"  # same as ARITHMETIC_SUBTRACT
    ARITHMETIC_POWER = "pow"
    ARITHMETIC_SQRT = "sqrt"
    ARITHMETIC_ABS = "abs"
    ARITHMETIC_RATE = "rate"


    # Relational
    EQUAL = "=="
    NOT_EQUAL = "!="
    GREATER_THAN = ">"
    LESS_THAN = "<"
    GREATER_THAN_OR_EQUAL = ">="
    LESS_THAN_OR_EQUAL = "<="

    # Logical
    LOGICAL_AND = "&&"
    LOGICAL_OR = "||"
    LOGICAL_XOR = "xor"
    LOGICAL_IMPLIES = "->"
    LOGICAL_EQUIV = "<->"
    LOGICAL_NEGATE = "!"

    # Future-time
    GLOBAL = "G"
    FUTURE = "F"
    UNTIL = "U"
    RELEASE = "R"

    # Past-time
    HISTORICAL = "H"
    ONCE = "O"
    SINCE = "S"
    TRIGGER = "T"

    # Other
    COUNT = "count"
    PREVIOUS = "prev"


    def is_booleanizer_operator(self) -> bool:
        return self in {
            OperatorKind.BITWISE_AND,
            OperatorKind.BITWISE_OR,
            OperatorKind.BITWISE_XOR,
            OperatorKind.BITWISE_NEGATE,
            OperatorKind.SHIFT_LEFT,
            OperatorKind.SHIFT_RIGHT,
            OperatorKind.ARITHMETIC_ADD,
            OperatorKind.ARITHMETIC_SUBTRACT,
            OperatorKind.ARITHMETIC_MULTPLY,
            OperatorKind.ARITHMETIC_DIVIDE,
            OperatorKind.ARITHMETIC_MODULO,
            OperatorKind.ARITHMETIC_NEGATE,
            OperatorKind.ARITHMETIC_POWER,
            OperatorKind.ARITHMETIC_SQRT,
            OperatorKind.ARITHMETIC_ABS,
            OperatorKind.ARITHMETIC_RATE,
            OperatorKind.GREATER_THAN,
            OperatorKind.GREATER_THAN_OR_EQUAL,
            OperatorKind.LESS_THAN,
            OperatorKind.LESS_THAN_OR_EQUAL,
            OperatorKind.COUNT,
        }


class Operator(Expression):
    def __init__(
        self,
        loc: log.FileLocation,
        op_kind: OperatorKind,
        children: list[Expression],
        type: types.Type = types.NoType(),
    ) -> None:
        super().__init__(loc, children, type)
        self.operator: OperatorKind = op_kind
        self.symbol: str = op_kind.value

        if is_temporal_operator(self) or is_logical_operator(self):
            self.engine = types.R2U2Engine.TEMPORAL_LOGIC
        else:
            self.engine = types.R2U2Engine.BOOLEANIZER

    @staticmethod
    def Count(
        loc: log.FileLocation,
        num: Expression,
        children: list[Expression],
        type: types.Type = types.NoType(),
    ) -> Operator:
        return Operator(loc, OperatorKind.COUNT, [num] + children, type)

    @staticmethod
    def BitwiseAnd(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.BITWISE_AND, [lhs, rhs])

    @staticmethod
    def BitwiseOr(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.BITWISE_OR, [lhs, rhs])

    @staticmethod
    def BitwiseXor(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.BITWISE_XOR, [lhs, rhs])

    @staticmethod
    def BitwiseNegate(loc: log.FileLocation, operand: Expression) -> Operator:
        return Operator(loc, OperatorKind.BITWISE_NEGATE, [operand])

    @staticmethod
    def ShiftLeft(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.SHIFT_LEFT, [lhs, rhs])

    @staticmethod
    def ShiftRight(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.SHIFT_RIGHT, [lhs, rhs])

    @staticmethod
    def ArithmeticAdd(
        loc: log.FileLocation,
        operands: list[Expression],
        type: types.Type = types.NoType(),
    ) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_ADD, operands, type)

    @staticmethod
    def ArithmeticSubtract(
        loc: log.FileLocation,
        lhs: Expression,
        rhs: Expression,
        type: types.Type = types.NoType(),
    ) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_SUBTRACT, [lhs, rhs], type)

    @staticmethod
    def ArithmeticMultiply(
        loc: log.FileLocation,
        operands: list[Expression],
        type: types.Type = types.NoType(),
    ) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_MULTPLY, operands, type)

    @staticmethod
    def ArithmeticDivide(
        loc: log.FileLocation,
        lhs: Expression,
        rhs: Expression,
        type: types.Type = types.NoType(),
    ) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_DIVIDE, [lhs, rhs], type)

    @staticmethod
    def ArithmeticModulo(
        loc: log.FileLocation,
        lhs: Expression,
        rhs: Expression,
        type: types.Type = types.NoType(),
    ) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_MODULO, [lhs, rhs], type)
    
    @staticmethod
    def ArithmeticPower(
        loc: log.FileLocation,
        lhs: Expression,
        rhs: Expression,
        type: types.Type = types.NoType(),
    ) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_POWER, [lhs, rhs], type)
    
    @staticmethod
    def ArithmeticSqrt(loc: log.FileLocation, operand: Expression) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_SQRT, [operand])
    
    @staticmethod
    def ArithmeticAbs(loc: log.FileLocation, operand: Expression) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_ABS, [operand])


    @staticmethod
    def ArithmeticNegate(loc: log.FileLocation, operand: Expression) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_NEGATE, [operand])
        
    @staticmethod
    def RateFunction(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_RATE, [lhs, rhs])
    
    @staticmethod
    def PreviousFunction(loc: log.FileLocation, operand: Expression) -> Operator:
        return Operator(loc, OperatorKind.PREVIOUS, [operand])

    @staticmethod
    def Equal(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.EQUAL, [lhs, rhs])

    @staticmethod
    def NotEqual(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.NOT_EQUAL, [lhs, rhs])

    @staticmethod
    def GreaterThan(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        return Operator(loc, OperatorKind.GREATER_THAN, [lhs, rhs])

    @staticmethod
    def LessThan(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        return Operator(loc, OperatorKind.LESS_THAN, [lhs, rhs])

    @staticmethod
    def GreaterThanOrEqual(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        return Operator(loc, OperatorKind.GREATER_THAN_OR_EQUAL, [lhs, rhs])

    @staticmethod
    def LessThanOrEqual(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        return Operator(loc, OperatorKind.LESS_THAN_OR_EQUAL, [lhs, rhs])

    @staticmethod
    def LogicalAnd(loc: log.FileLocation, operands: list[Expression]) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_AND, operands)
        operator.bpd = min([opnd.bpd for opnd in operands])
        operator.wpd = max([opnd.wpd for opnd in operands])
        return operator

    @staticmethod
    def LogicalOr(loc: log.FileLocation, operands: list[Expression]) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_OR, operands)
        operator.bpd = min([opnd.bpd for opnd in operands])
        operator.wpd = max([opnd.wpd for opnd in operands])
        return operator

    @staticmethod
    def LogicalXor(loc: log.FileLocation, operands: list[Expression]) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_XOR, operands)
        operator.bpd = min([opnd.bpd for opnd in operands])
        operator.wpd = max([opnd.wpd for opnd in operands])
        return operator

    @staticmethod
    def LogicalIff(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_EQUIV, [lhs, rhs])
        operator.bpd = min([opnd.bpd for opnd in [lhs, rhs]])
        operator.wpd = max([opnd.wpd for opnd in [lhs, rhs]])
        return operator

    @staticmethod
    def LogicalImplies(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_IMPLIES, [lhs, rhs])
        operator.bpd = min([opnd.bpd for opnd in [lhs, rhs]])
        operator.wpd = max([opnd.wpd for opnd in [lhs, rhs]])
        return operator

    @staticmethod
    def LogicalNegate(loc: log.FileLocation, operand: Expression) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_NEGATE, [operand])
        operator.bpd = operand.bpd
        operator.wpd = operand.wpd
        return operator

    def __deepcopy__(self, memo) -> Operator:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = Operator(self.loc, self.operator, children)
        self.copy_attrs(new)
        return new
    
class Atomic(Expression):
    def __init__(
        self, loc: log.FileLocation, child: Expression
    ) -> None:
        super().__init__(loc, [child])
        self.engine = types.R2U2Engine.BOOLEANIZER

    def __deepcopy__(self, memo):
        new = Atomic(self.loc, self.children[0])
        self.copy_attrs(new)
        return new


class TemporalOperator(Operator):
    def __init__(
        self,
        loc: log.FileLocation,
        operator: OperatorKind,
        lb: int,
        ub: int,
        children: list[Expression],
    ) -> None:
        super().__init__(loc, operator, children)
        self.interval = types.Interval(lb, ub)
        self.symbol = f"{operator.value}[{lb},{ub}]"

    @staticmethod
    def Global(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.GLOBAL, lb, ub, [operand])
        operator.bpd = operand.bpd + lb
        operator.wpd = operand.wpd + ub
        return operator

    @staticmethod
    def Future(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.FUTURE, lb, ub, [operand])
        operator.bpd = operand.bpd + lb
        operator.wpd = operand.wpd + ub
        operator.symbol = f"F[{lb},{ub}]"
        return operator

    @staticmethod
    def Until(
        loc: log.FileLocation, lb: int, ub: int, lhs: Expression, rhs: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.UNTIL, lb, ub, [lhs, rhs])
        operator.bpd = min([opnd.bpd for opnd in [lhs, rhs]]) + lb
        operator.wpd = max([opnd.wpd for opnd in [lhs, rhs]]) + ub
        return operator

    @staticmethod
    def Release(
        loc: log.FileLocation, lb: int, ub: int, lhs: Expression, rhs: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.RELEASE, lb, ub, [lhs, rhs])
        operator.bpd = min([opnd.bpd for opnd in [lhs, rhs]]) + lb
        operator.wpd = max([opnd.wpd for opnd in [lhs, rhs]]) + ub
        return operator

    @staticmethod
    def Historical(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.HISTORICAL, lb, ub, [operand])
        operator.bpd = operand.bpd - ub
        operator.wpd = operand.bpd - lb
        return operator

    @staticmethod
    def Once(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.ONCE, lb, ub, [operand])
        operator.bpd = operand.bpd - ub
        operator.wpd = operand.bpd - lb
        return operator

    @staticmethod
    def Since(
        loc: log.FileLocation, lb: int, ub: int, lhs: Expression, rhs: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.SINCE, lb, ub, [lhs, rhs])
        operator.bpd = min([opnd.bpd for opnd in [lhs, rhs]]) - lb
        operator.wpd = max([opnd.wpd for opnd in [lhs, rhs]]) - lb
        return operator
    
    @staticmethod
    def Trigger(
        loc: log.FileLocation, lb: int, ub: int, lhs: Expression, rhs: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.TRIGGER, lb, ub, [lhs, rhs])
        operator.bpd = min([opnd.bpd for opnd in [lhs, rhs]]) - lb
        operator.wpd = max([opnd.wpd for opnd in [lhs, rhs]]) - lb
        return operator

    def __deepcopy__(self, memo) -> Operator:
        children = [copy.deepcopy(c, memo) for c in self.children]
        new = TemporalOperator(
            self.loc, self.operator, self.interval.lb, self.interval.ub, children
        )
        self.copy_attrs(new)
        return new


# Helpful predicates -- especially for type checking
def is_operator(expr: Expression, operator: OperatorKind) -> bool:
    """Returns True if `expr` is an `Operator` of type `operator`."""
    return isinstance(expr, Operator) and expr.operator is operator


def is_commutative_operator(expr) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.LOGICAL_AND,
        OperatorKind.LOGICAL_OR,
        OperatorKind.LOGICAL_XOR,
        OperatorKind.LOGICAL_EQUIV,
        OperatorKind.BITWISE_AND,
        OperatorKind.BITWISE_OR,
        OperatorKind.BITWISE_XOR,
        OperatorKind.ARITHMETIC_ADD,
        OperatorKind.ARITHMETIC_MULTPLY,
        OperatorKind.EQUAL,
        OperatorKind.NOT_EQUAL,
    }


def is_multi_arity_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.LOGICAL_AND,
        OperatorKind.LOGICAL_OR,
        OperatorKind.ARITHMETIC_ADD,
        OperatorKind.ARITHMETIC_MULTPLY,
    }


def is_bitwise_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.BITWISE_AND,
        OperatorKind.BITWISE_OR,
        OperatorKind.BITWISE_XOR,
        OperatorKind.BITWISE_NEGATE,
    }


def is_arithmetic_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.ARITHMETIC_ADD,
        OperatorKind.ARITHMETIC_SUBTRACT,
        OperatorKind.ARITHMETIC_DIVIDE,
        OperatorKind.ARITHMETIC_MULTPLY,
        OperatorKind.ARITHMETIC_MODULO,
        OperatorKind.ARITHMETIC_NEGATE,
        OperatorKind.ARITHMETIC_POWER,
        OperatorKind.ARITHMETIC_SQRT,
        OperatorKind.ARITHMETIC_ABS,
        OperatorKind.ARITHMETIC_RATE,
    }


def is_relational_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.EQUAL,
        OperatorKind.NOT_EQUAL,
        OperatorKind.GREATER_THAN,
        OperatorKind.LESS_THAN,
        OperatorKind.GREATER_THAN_OR_EQUAL,
        OperatorKind.LESS_THAN_OR_EQUAL,
    }


def is_logical_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.LOGICAL_AND,
        OperatorKind.LOGICAL_OR,
        OperatorKind.LOGICAL_XOR,
        OperatorKind.LOGICAL_IMPLIES,
        OperatorKind.LOGICAL_EQUIV,
        OperatorKind.LOGICAL_NEGATE,
    }


def is_future_time_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.GLOBAL,
        OperatorKind.FUTURE,
        OperatorKind.UNTIL,
        OperatorKind.RELEASE,
    }


def is_past_time_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.HISTORICAL,
        OperatorKind.ONCE,
        OperatorKind.SINCE,
        OperatorKind.TRIGGER,
    }

def is_prev_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.PREVIOUS,
    }

def is_temporal_operator(expr: Expression) -> bool:
    return is_future_time_operator(expr) or is_past_time_operator(expr)


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

    def __str__(self) -> str:
        return "spec_set"


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
        return self.symbol + ": {" + " ".join(members_str_list) + "}"


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


class SpecSection(Node):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc)
        self.specs = specs


class FutureTimeSpecSection(SpecSection):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc, specs)

    def __str__(self) -> str:
        return "FTSPEC\n\t" + "\n\t".join([str(spec) for spec in self.specs])


class PastTimeSpecSection(SpecSection):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc, specs)

    def __str__(self) -> str:
        return "PTSPEC\n\t" + "\n\t".join([str(spec) for spec in self.specs])


ProgramSection = Union[
    StructSection, InputSection, DefineSection, SpecSection
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

        self.total_scq_size = -1

        # Minimum values for bounds in bounds.h and config.toml
        self.bounds_c = {
            "R2U2_MAX_INSTRUCTIONS": -1,
            "R2U2_MAX_SIGNALS": -1,
            "R2U2_MAX_ATOMICS": -1,
            "R2U2_MAX_INST_LEN": -1,
            "R2U2_MAX_BZ_INSTRUCTIONS": -1,
            "R2U2_MAX_AUX_STRINGS": -1,
            "R2U2_SCQ_BYTES": -1,
            "R2U2_FLOAT_EPSILON": 0.00001,
        }

        self.bounds_rs = {
            "R2U2_MAX_SPECS": -1,
            "R2U2_MAX_SIGNALS": -1,
            "R2U2_MAX_ATOMICS": -1,
            "R2U2_MAX_BZ_INSTRUCTIONS": -1,
            "R2U2_MAX_TL_INSTRUCTIONS": -1,
            "R2U2_TOTAL_QUEUE_MEM": -1,
        }

    def get_bounds_c_file(self) -> str:
        """Returns the contents of the bounds.h file."""
        contents =  "#ifndef R2U2_BOUNDS_H\n"
        contents += "#define R2U2_BOUNDS_H\n"
        contents += "\n".join(
            [
                f"#define {key} {value:F}"
                if type(value) is float
                else f"#define {key} {value}"
                for key, value in self.bounds_c.items()
            ]
        )
        contents += "\n#endif\n"
        return contents

    def get_bounds_rs_file(self) -> str:
        """Returns the contents of the config.toml file."""
        contents =  "[env]\n"
        contents += "\n".join(
            [
                f'{key} = {{ value = "{value}", force = true }}'
                for key, value in self.bounds_rs.items()
            ]
        )
        return contents


    def replace_spec(self, spec: Specification, new: list[Specification]) -> None:
        """Replaces `spec` with `new` in this `Program`, if `spec` is present. Raises `KeyError` if `spec` is not present."""
        try:
            index = self.ft_spec_set.children.index(spec)
            self.ft_spec_set.children[index : index + 1] = new
        except ValueError:
            index = self.pt_spec_set.children.index(spec)
            self.pt_spec_set.children[index : index + 1] = new

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

    def __repr__(self) -> str:
        return "\n".join([repr(s) for s in self.get_specs()])


class Context:
    def __init__(self, opts: options.Options) -> None:
        self.options = opts
        self.definitions: dict[str, Expression] = {}
        self.structs: dict[str, dict[str, types.Type]] = {}
        self.signals: dict[str, types.Type] = {}
        self.variables: dict[str, types.Type] = {}
        self.specifications: dict[str, Formula] = {}
        self.contracts: dict[str, Contract] = {}
        self.atomic_id: dict[Expression, int] = {}
        self.bound_vars: dict[str, ArrayExpression] = {}

        self.is_ft = False
        self.has_future_time = False
        self.has_past_time = False
        self.status = True

    def get_symbols(self) -> list[str]:
        symbols = [s for s in self.definitions.keys()]
        symbols += [s for s in self.structs.keys()]
        symbols += [s for s in self.signals.keys()]
        symbols += [s for s in self.variables.keys()]
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


def to_infix_str(start: Expression) -> str:
    s = ""

    stack: list[tuple[int, Expression]] = []
    stack.append((0, start))

    while len(stack) > 0:
        (seen, expr) = stack.pop()

        if isinstance(expr, (Constant, Variable, Signal)):
            s += expr.symbol
        elif isinstance(expr, ArrayIndex):
            if seen == 0:
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            elif seen == 1:
                s += f"[{expr.index}]"
        elif isinstance(expr, StructAccess):
            if seen == 0:
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                s += f".{expr.member}"
        elif isinstance(expr, ArrayExpression):
            if seen == len(expr.children):
                s += "}"
            elif seen == 0:
                s += "{"
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                s += ","
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
        elif isinstance(expr, (Struct, FunctionCall)) or is_operator(
            expr, OperatorKind.COUNT
        ):
            if seen == len(expr.children):
                s += ")"
            elif seen == 0:
                s += f"{expr.symbol}("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                s += ","
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
        elif isinstance(expr, SetAggregation):
            if seen == 0:
                s += f"{expr.symbol}({expr.bound_var}:"
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_set()))
            elif seen == 1:
                s += ")("
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_expr()))
            else:
                s += ")"
        elif isinstance(expr, Operator) and len(expr.children) == 1:
            if seen == 0:
                s += f"{expr.symbol}("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                s += ")"
        elif isinstance(expr, Operator) and len(expr.children) == 2:
            if seen == 0:
                s += "("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            elif seen == 1:
                s += f"){expr.symbol}("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[1]))
            else:
                s += ")"
        elif isinstance(expr, Operator):
            if seen == len(expr.children):
                s += ")"
            elif seen == 0:
                s += "("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
            else:
                s += f"){expr.symbol}("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
        elif isinstance(expr, Atomic):
            if seen == 0:
                s += "("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                s += ")"
        elif isinstance(expr, Formula):
            if seen == 0:
                s += str(expr.formula_number) if expr.symbol[0] == "#" else expr.symbol
                s += ":"
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_expr()))
            else:
                s += ";"
        elif isinstance(expr, Contract):
            if seen == 0:
                s += f"{expr.symbol}: ("
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_assumption()))
            elif seen == 1:
                s += ")=>("
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_guarantee()))
            else:
                s += ")"
        else:
            log.error(MODULE_CODE, f"Bad str ({expr})")
            return ""

    return s


def to_prefix_str(start: Expression) -> str:
    s = ""

    stack: list["tuple[int, Expression]"] = []
    stack.append((0, start))

    while len(stack) > 0:
        (seen, expr) = stack.pop()

        if isinstance(expr, (Constant, Variable, Signal)):
            s += expr.symbol + " "
        elif isinstance(expr, StructAccess):
            if seen == 0:
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                s = s[:-1] + f".{expr.member} "
        elif isinstance(expr, ArrayExpression):
            if seen == 0:
                s += "{"
                stack.append((seen + 1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                s = s[:-1] + "} "
        elif isinstance(expr, ArrayIndex):
            if seen == 0:
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            elif seen == 1:
                s = s[:-1] + f"[{expr.index}] "
        elif isinstance(expr, (Struct, FunctionCall)) or is_operator(
            expr, OperatorKind.COUNT
        ):
            if seen == len(expr.children):
                s = s[:-1] + ") "
            elif seen == 0:
                s += f"{expr.symbol}("
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                s += ","
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
        elif isinstance(expr, SetAggregation):
            if seen == 0:
                s += f"{expr.symbol}({expr.bound_var}:"
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_set()))
            elif seen == 1:
                s = s[:-1] + ")("
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_expr()))
            else:
                s = s[:-1] + ")"
        elif isinstance(expr, Operator):
            if seen == 0:
                s += f"({expr.symbol} "
                stack.append((seen + 1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                s = s[:-1] + ") "
        elif isinstance(expr, Atomic):
            if seen == 0:
                s += "("
                stack.append((seen + 1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                s = s[:-1] + ") "
        elif isinstance(expr, Formula):
            s += expr.symbol
            s += ": "
            stack.append((0, expr.get_expr()))
        elif isinstance(expr, Contract):
            if seen == 0:
                s += f"{expr.symbol}: ("
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_assumption()))
            elif seen == 1:
                s += ") => ("
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_guarantee()))
            else:
                s = s[:-1] + ")"
        elif isinstance(expr, SpecificationSet):
            [stack.append((0, spec)) for spec in reversed(expr.get_specs())]
        else:
            log.error(MODULE_CODE, f"Bad repr ({expr})")
            return ""

    return s[:-1]


def to_mltl_std(program: Program, context: Context) -> str:
    mltl = ""

    stack: list[tuple[int, Expression]] = []

    for spec in program.get_specs():
        if isinstance(spec, Contract):
            log.warning(MODULE_CODE, "Cannot express AGCs in MLTL standard, skipping")
            continue

        stack.append((0, spec.get_expr()))

        while len(stack) > 0:
            (seen, expr) = stack.pop()

            if isinstance(expr, Constant):
                mltl += expr.symbol + " "
            elif expr in context.atomic_id:
                mltl += f"a{context.atomic_id[expr]}"
            elif len(expr.children) == 1 and (
                is_temporal_operator(expr) or is_logical_operator(expr)
            ):
                if seen == 0:
                    mltl += f"{expr.symbol}("
                    stack.append((seen + 1, expr))
                    stack.append((0, expr.children[0]))
                else:
                    mltl += ")"
            elif is_temporal_operator(expr) or is_logical_operator(expr):
                if seen == len(expr.children):
                    mltl += ")"
                elif seen == 0:
                    mltl += "("
                    stack.append((seen + 1, expr))
                    stack.append((0, expr.children[seen]))
                else:
                    if is_operator(expr, OperatorKind.LOGICAL_AND):
                        symbol = "&"
                    elif is_operator(expr, OperatorKind.LOGICAL_OR):
                        symbol = "|"
                    else:
                        symbol = expr.symbol

                    mltl += f"){symbol}("
                    stack.append((seen + 1, expr))
                    stack.append((0, expr.children[seen]))
            else:
                log.error(
                    MODULE_CODE, f"Expression incompatible with MLTL standard ({expr})"
                )
                return ""

        mltl += "\n"

    return mltl
