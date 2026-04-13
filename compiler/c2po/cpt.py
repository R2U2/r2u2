"""C2PO Parse Tree (CPT) represents structure of a .c2po or .mltl file."""
from __future__ import annotations
import enum
import pickle
import re
from typing import Iterator, Optional, Union, cast, Any, NamedTuple, Callable
from c2po import log, types, stats

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
        set_parents: bool = True
    ) -> None:
        super().__init__(loc)
        self.engine = types.R2U2Engine.NONE
        self.scq_size: int = -1
        self.bpd: int = 0
        self.wpd: int = 0
        self.scq: tuple[int, int] = (-1, -1)
        self.type: types.Type = type

        self.children: list[Expression] = []
        self.parents: set[Expression] = set()

        # If set_parents is False, we don't want to set parents when adding children.
        # This is used when an expression is a "dummy" expression used for the SAT encoding
        # or generally any expression that is not part of the final program.
        for child in children:
            self.children.append(child)
            if set_parents:
                child.parents.add(self)

        # Used for pre-order traversal, if this has been replaced during traversal
        self.replacement: Optional[Expression] = None

    def get_siblings(self) -> set[Expression]:
        siblings = set()

        for parent in self.parents:
            for sibling in [s for s in parent.children]:
                if sibling == self:
                    continue
                siblings.add(sibling)

        return siblings

    def get_descendants(self) -> list[Expression]:
        prev_visited_children: list[Expression] = [self]
        visited_children: list[Expression] = []
        children: list[Expression] = []
        while True:
            for node in prev_visited_children:
                for child in node.children:
                    if not isinstance(child, SpecificationSet):
                        visited_children.append(child)
                        children.append(child)
            if len(visited_children) == 0:
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
            new.parents.add(parent)

        for child in self.children:
            if self in child.parents:
                child.parents.remove(self)

        self.replacement = new
        new.type = self.type

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
        new.bpd = self.bpd
        new.wpd = self.wpd
        new.scq = self.scq
        new.type = self.type

    def __str__(self) -> str:
        return to_infix_str(self)

    def __repr__(self) -> str:
        return to_prefix_str(self, with_internal_labels=True)

    def deepcopy(self, context: Context) -> Expression:
        return deepcopy_expr(self, context, {})

class Match(Expression):
    def __init__(self, loc: log.FileLocation, name: str, match_function: Callable[[str], bool]) -> None:
        super().__init__(loc, [])
        self.match_function = match_function
        self.symbol = name

    def matches(self, arg: str) -> bool:
        return self.match_function(arg)

    def __str__(self) -> str:
        return self.symbol

    def __repr__(self) -> str:
        return self.symbol

class Constant(Expression):
    def __init__(self, loc: log.FileLocation, value: Any) -> None:
        super().__init__(loc, [])
        self.value: bool = value
        self.symbol = str(value)

        if isinstance(value, bool):
            self.type = types.BoolType(True)
        elif isinstance(value, int):
            self.type = types.IntType(True)
        elif isinstance(value, float):
            self.type = types.FloatType(True)
        else:
            raise ValueError(f"Bad value ({value})")

        if types.is_bool_type(self.type):
            self.engine = types.R2U2Engine.TEMPORAL_LOGIC
        else:
            self.engine = types.R2U2Engine.BOOLEANIZER

class MissionTime(Expression):
    """MissionTime is a special variable that represents the symbolic mission time. This is only
    used in equivalence checking when the input format is .equiv. It is not used in any other
    context.
    
    For other contexts, users set the mission time using the '--mission-time' option and is expanded
    to a constant during parsing."""

    def __init__(self, loc: log.FileLocation) -> None:
        super().__init__(loc, [])
        self.symbol = "M"
        self.type = types.IntType(True)

class CurrentTimestamp(Expression):
    first_time_seen = True

    def __init__(self, loc: log.FileLocation) -> None:
        super().__init__(loc, [])
        self.engine = types.R2U2Engine.BOOLEANIZER
        self.symbol = "TAU"
        
        if CurrentTimestamp.first_time_seen and types.IntType.is_signed:
            log.warning(
                "by default, r2u2_time is an _unsigned_ 32-bit integer and r2u2_int is a _signed_ 32-bit integer in R2U2",
                loc,
            )
        CurrentTimestamp.first_time_seen = False

class Variable(Expression):
    """Variables represent bound variables in set aggregations."""
    def __init__(self, loc: log.FileLocation, s: str) -> None:
        super().__init__(loc, [])
        self.symbol: str = s

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Variable) and __o.symbol == self.symbol

    def __hash__(self) -> int:
        # TODO: Check that this is correct, seems like if two objects are equal their hashes should
        # be the same

        # note how this compares to __eq__
        # we hash the id so that in sets/dicts different
        # instances of the same variable are distinct
        return id(self)

class Signal(Expression):
    def __init__(self, loc: log.FileLocation, s: str, t: types.Type) -> None:
        super().__init__(loc, [])
        self.symbol: str = s
        self.type: types.Type = t
        self.signal_id: int = -1

class SymbolicIntervalVariable(Expression):
    """SymbolicIntervalVariables are used when defining symbolic intervals and their constraints. They
    are only used in the context of equivalence checking when the input format is .equiv."""
    def __init__(self, loc: log.FileLocation, s: str) -> None:
        super().__init__(loc, [])
        self.symbol: str = s
        self.type = types.IntType(True)

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SymbolicIntervalVariable) and __o.symbol == self.symbol

    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        return self.symbol

    def __repr__(self) -> str:
        return f"IntervalBoundVariable({self.symbol})"

class ArrayExpression(Expression):
    def __init__(self, loc: log.FileLocation, members: list[Expression]) -> None:
        super().__init__(loc, members)
        self.max_size: int = len(members)

class ArrayIndex(Expression):
    def __init__(self, loc: log.FileLocation, array: Expression, index: int) -> None:
        super().__init__(loc, [array])
        self.index = index
        self.symbol = "[]"

    def get_array(self) -> Expression:
        return self.children[0]

    def get_index(self) -> int:
        return self.index

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
                f"member '{name}' not in members of '{self.symbol}'",
            )
            return None

        member = self.children[self.members[name]]

        if member is None:
            log.internal(
                f"member '{name}' not in members of '{self.symbol}'",
            )
            return None

        return cast(Expression, member)

class StructAccess(Expression):
    def __init__(self, loc: log.FileLocation, struct: Expression, member: str) -> None:
        super().__init__(loc, [struct])
        self.member: str = member
        self.symbol = "."

    def get_struct(self) -> Struct:
        return cast(Struct, self.children[0])

class FunctionCall(Expression):
    def __init__(
        self, loc: log.FileLocation, s: str, operands: list[Expression]
    ) -> None:
        super().__init__(loc, operands)
        self.symbol: str = s

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
        self.type = types.BoolType()
        self.symbol = operator.value

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

    def get_num(self) -> Optional[Expression]:
        if len(self.children) < 4:
            return None
        return cast(Expression, self.children[1])

    def get_set(self) -> ArrayExpression:
        return cast(ArrayExpression, self.children[0])

    def get_expr(self) -> Expression:
        """Returns the aggregated `Expression`. This is always the last child, see docstring of `SetAggregation` for a visual."""
        return cast(Expression, self.children[-1])

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
    ARITHMETIC_MULTIPLY = "*"
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
    MIN = "min"
    MAX = "max"

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
            OperatorKind.ARITHMETIC_MULTIPLY,
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

    def is_extended_operator(self) -> bool:
        return self in {
            OperatorKind.LOGICAL_XOR,
            OperatorKind.LOGICAL_IMPLIES,
            OperatorKind.FUTURE,
            OperatorKind.GLOBAL,
            OperatorKind.HISTORICAL,
        }

class Operator(Expression):
    def __init__(
        self,
        loc: log.FileLocation,
        op_kind: OperatorKind,
        children: list[Expression],
        type: types.Type = types.NoType(),
        set_parents: bool = True
    ) -> None:
        super().__init__(loc, children, type, set_parents)
        self.operator: OperatorKind = op_kind
        self.symbol: str = op_kind.value

        self.wpd = max([c.wpd for c in children])
        self.bpd = min([c.bpd for c in children])

        if is_temporal_operator(self) or is_logical_operator(self):
            self.engine = types.R2U2Engine.TEMPORAL_LOGIC
        else:
            self.engine = types.R2U2Engine.BOOLEANIZER

    @staticmethod
    def Min(loc: log.FileLocation, operands: list[Expression]) -> Operator:
        new = Operator(loc, OperatorKind.MIN, operands)
        new.type = types.IntType()
        return new

    @staticmethod
    def Max(loc: log.FileLocation, operands: list[Expression]) -> Operator:
        new = Operator(loc, OperatorKind.MAX, operands)
        new.type = types.IntType()
        return new  

    @staticmethod
    def Count(
        loc: log.FileLocation,
        num: Expression,
        children: list[Expression],
        type: types.Type = types.NoType(),
    ) -> Operator:
        new = Operator(loc, OperatorKind.COUNT, [num] + children, type)
        new.type = types.IntType()
        return new

    @staticmethod
    def BitwiseAnd(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        new = Operator(loc, OperatorKind.BITWISE_AND, [lhs, rhs])
        new.type = types.IntType()
        return new

    @staticmethod
    def BitwiseOr(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        new = Operator(loc, OperatorKind.BITWISE_OR, [lhs, rhs])
        new.type = types.IntType()
        return new

    @staticmethod
    def BitwiseXor(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        new = Operator(loc, OperatorKind.BITWISE_XOR, [lhs, rhs])
        new.type = types.IntType()
        return new

    @staticmethod
    def BitwiseNegate(loc: log.FileLocation, operand: Expression) -> Operator:
        new = Operator(loc, OperatorKind.BITWISE_NEGATE, [operand])
        new.type = types.IntType()
        return new

    @staticmethod
    def ShiftLeft(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        new = Operator(loc, OperatorKind.SHIFT_LEFT, [lhs, rhs])
        new.type = types.IntType()
        return new

    @staticmethod
    def ShiftRight(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        new = Operator(loc, OperatorKind.SHIFT_RIGHT, [lhs, rhs])
        new.type = types.IntType()
        return new

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
        return Operator(loc, OperatorKind.ARITHMETIC_MULTIPLY, operands, type)

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
        new = Operator(loc, OperatorKind.ARITHMETIC_MODULO, [lhs, rhs], type)
        new.type = types.IntType()
        return new

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
    def RateFunction(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        return Operator(loc, OperatorKind.ARITHMETIC_RATE, [lhs, rhs])

    @staticmethod
    def PreviousFunction(loc: log.FileLocation, operand: Expression) -> Operator:
        return Operator(loc, OperatorKind.PREVIOUS, [operand])

    @staticmethod
    def Equal(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        operator = Operator(loc, OperatorKind.EQUAL, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def NotEqual(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        operator = Operator(loc, OperatorKind.NOT_EQUAL, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def GreaterThan(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        operator = Operator(loc, OperatorKind.GREATER_THAN, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LessThan(loc: log.FileLocation, lhs: Expression, rhs: Expression) -> Operator:
        operator = Operator(loc, OperatorKind.LESS_THAN, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def GreaterThanOrEqual(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        operator = Operator(loc, OperatorKind.GREATER_THAN_OR_EQUAL, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LessThanOrEqual(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        operator = Operator(loc, OperatorKind.LESS_THAN_OR_EQUAL, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LogicalAnd(loc: log.FileLocation, operands: list[Expression], set_parents: bool = True) -> Operator:
        # We use LogicalAnd in the SAT encoding (for encoding the conjunction of all
        # specifications), so we may not want to set parents
        operator = Operator(loc, OperatorKind.LOGICAL_AND, operands, set_parents=set_parents)
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LogicalOr(loc: log.FileLocation, operands: list[Expression]) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_OR, operands)
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LogicalXor(loc: log.FileLocation, operands: list[Expression]) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_XOR, operands)
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LogicalIff(
        loc: log.FileLocation,
        lhs: Expression,
        rhs: Expression,
        set_parents: bool = True,
    ) -> Operator:
        # We use LogicalIff in the SAT encoding, so we may not want to set parents
        operator = Operator(
            loc, OperatorKind.LOGICAL_EQUIV, [lhs, rhs], set_parents=set_parents
        )
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LogicalImplies(
        loc: log.FileLocation, lhs: Expression, rhs: Expression
    ) -> Operator:
        operator = Operator(loc, OperatorKind.LOGICAL_IMPLIES, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def LogicalNegate(
        loc: log.FileLocation, operand: Expression, set_parents: bool = True
    ) -> Operator:
        # We use LogicalNegate in the SAT encoding, so we may not want to set parents
        operator = Operator(
            loc, OperatorKind.LOGICAL_NEGATE, [operand], set_parents=set_parents
        )
        operator.type = types.BoolType()
        return operator

class Atomic(Expression):
    def __init__(self, loc: log.FileLocation, child: Expression) -> None:
        super().__init__(loc, [child])
        self.engine = types.R2U2Engine.BOOLEANIZER
        self.type = types.BoolType()

    def get_expr(self) -> Expression:
        return cast(Expression, self.children[0])

    def __repr__(self) -> str:
        return f"Atomic({repr(self.children[0])})"

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
        self.interval = ConcreteInterval(lb, ub)
        self.symbol = f"{operator.value}[{lb},{ub}]"
        self.bpd = min([c.bpd for c in children]) + lb
        self.wpd = max([c.wpd for c in children]) + ub

    @staticmethod
    def Global(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.GLOBAL, lb, ub, [operand])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Future(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.FUTURE, lb, ub, [operand])
        operator.symbol = f"F[{lb},{ub}]"
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Until(
        loc: log.FileLocation, lb: int, ub: int, lhs: Expression, rhs: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.UNTIL, lb, ub, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Release(
        loc: log.FileLocation, lb: int, ub: int, lhs: Expression, rhs: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.RELEASE, lb, ub, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Historical(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.HISTORICAL, lb, ub, [operand])
        operator.type = types.BoolType()
        operator.bpd = operand.bpd - ub
        operator.wpd = operand.bpd - lb
        return operator

    @staticmethod
    def Once(
        loc: log.FileLocation, lb: int, ub: int, operand: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.ONCE, lb, ub, [operand])
        operator.type = types.BoolType()
        operator.bpd = operand.bpd - ub
        operator.wpd = operand.bpd - lb
        return operator

    @staticmethod
    def Since(
        loc: log.FileLocation, lb: int, ub: int, lhs: Expression, rhs: Expression
    ) -> TemporalOperator:
        operator = TemporalOperator(loc, OperatorKind.SINCE, lb, ub, [lhs, rhs])
        operator.type = types.BoolType()
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

class SymbolicTemporalOperator(Operator):
    """SymbolicTemporalOperators are the same as TemporalOperators, but their interval is symbolic.
    
    They are only used in the context of equivalence checking when the input format is .equiv."""
    def __init__(
        self,
        loc: log.FileLocation,
        operator: OperatorKind,
        lb: Expression,
        ub: Expression,
        children: list[Expression],
    ) -> None:
        super().__init__(loc, operator, children)
        self.interval = SymbolicInterval(lb, ub)
        self.symbol = f"{operator.value}[{lb},{ub}]"

    @staticmethod
    def Global(
        loc: log.FileLocation, lb: Expression, ub: Expression, operand: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.GLOBAL, lb, ub, [operand])
        operator.type = types.BoolType()   
        return operator

    @staticmethod
    def Future(
        loc: log.FileLocation, lb: Expression, ub: Expression, operand: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.FUTURE, lb, ub, [operand])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Until(
        loc: log.FileLocation, lb: Expression, ub: Expression, lhs: Expression, rhs: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.UNTIL, lb, ub, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Release(
        loc: log.FileLocation, lb: Expression, ub: Expression, lhs: Expression, rhs: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.RELEASE, lb, ub, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Historical(
        loc: log.FileLocation, lb: Expression, ub: Expression, operand: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.HISTORICAL, lb, ub, [operand])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Once(
        loc: log.FileLocation, lb: Expression, ub: Expression, operand: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.ONCE, lb, ub, [operand])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Since(
        loc: log.FileLocation, lb: Expression, ub: Expression, lhs: Expression, rhs: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.SINCE, lb, ub, [lhs, rhs])
        operator.type = types.BoolType()
        return operator

    @staticmethod
    def Trigger(
        loc: log.FileLocation, lb: Expression, ub: Expression, lhs: Expression, rhs: Expression
    ) -> SymbolicTemporalOperator:
        operator = SymbolicTemporalOperator(loc, OperatorKind.TRIGGER, lb, ub, [lhs, rhs])
        return operator

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
        OperatorKind.ARITHMETIC_MULTIPLY,
        OperatorKind.EQUAL,
        OperatorKind.NOT_EQUAL,
    }

def is_multi_arity_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.LOGICAL_AND,
        OperatorKind.LOGICAL_OR,
        OperatorKind.ARITHMETIC_ADD,
        OperatorKind.ARITHMETIC_MULTIPLY,
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
        OperatorKind.ARITHMETIC_MULTIPLY,
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

def is_min_max_operator(expr: Expression) -> bool:
    return isinstance(expr, Operator) and expr.operator in {
        OperatorKind.MIN,
        OperatorKind.MAX,
    }

def is_temporal_operator(expr: Expression) -> bool:
    return is_future_time_operator(expr) or is_past_time_operator(expr)

class ConcreteInterval(NamedTuple):
    lb: int
    ub: int

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, ConcreteInterval) and self.lb == __value.lb and self.ub == __value.ub

class SymbolicInterval(NamedTuple):
    lb: Expression
    ub: Expression

    def __eq__(self, __value: object) -> bool:
        return (
            isinstance(__value, SymbolicInterval)
            and str(self.lb) == str(__value.lb)
            and str(self.ub) == str(__value.ub)
        )

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

    def is_internal_label(self) -> bool:
        """Returns True if the label is an internal label, False otherwise.
        
        An internal label is a label that is generated by the compiler and is not intended to be used by the user.
        It is typically prefixed with '__' and suffixed with '__' (ex: '__f1__', '__p1__').
        """
        return re.match(r'^__.*__$', self.symbol) is not None

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

Specification = Union[Formula, Contract]

def get_spec_str_reference(spec: Specification) -> str:
    """Returns the `symbol` of `spec` if it is not an internal label, otherwise returns a string representation of the `spec` without the trailing semicolon."""
    if isinstance(spec, Formula) and not spec.is_internal_label():
        return spec.symbol
    return str(spec)[:-1] # remove the trailing semicolon

class SpecificationSet(Expression):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc, cast("list[Expression]", specs))

    def get_specs(self) -> list[Specification]:
        return cast("list[Specification]", self.children)

    def __str__(self) -> str:
        return "spec_set"

    def deepcopy(self, context: Context) -> SpecificationSet:
        children = [c.deepcopy(context) for c in self.children]
        new = SpecificationSet(self.loc, cast("list[Specification]", children))
        self.copy_attrs(new)
        return new

class StructDefinition(Node):
    def __init__(
        self, loc: log.FileLocation, symbol: str, var_decls: list[VariableDeclaration]
    ) -> None:
        super().__init__(loc)
        self.symbol = symbol
        self.var_decls = var_decls
        self.members: dict[str, types.Type] = {}
        for var_decl in var_decls:
            for sym in var_decl.variables:
                self.members[sym] = var_decl.type

    def __str__(self) -> str:
        members_str_list = [str(s) + ";" for s in self.var_decls]
        return self.symbol + ": {" + " ".join(members_str_list) + "}"

    def deepcopy(self, context: Context) -> StructDefinition:
        var_decls = [v.deepcopy(context) for v in self.var_decls]
        new = StructDefinition(self.loc, self.symbol, var_decls)
        return new

class VariableDeclaration(Node):
    def __init__(self, loc: log.FileLocation, vars: list[str], t: types.Type) -> None:
        super().__init__(loc)
        self.variables = vars
        self.type = t

    def __str__(self) -> str:
        return f"{','.join(self.variables)}: {str(self.type)}"

    def deepcopy(self, context: Context) -> VariableDeclaration:
        variables = [str(v) for v in self.variables]
        new = VariableDeclaration(self.loc, variables, self.type)
        return new

class Definition(Node):
    def __init__(self, loc: log.FileLocation, symbol: str, expr: Expression) -> None:
        super().__init__(loc)
        self.symbol = symbol
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.symbol} := {self.expr}"

    def deepcopy(self, context: Context) -> Definition:
        new = Definition(self.loc, self.symbol, self.expr.deepcopy(context))
        return new

class StructSection(Node):
    def __init__(
        self, loc: log.FileLocation, struct_defs: list[StructDefinition]
    ) -> None:
        super().__init__(loc)
        self.struct_defs = struct_defs

    def __str__(self) -> str:
        structs_str_list = [str(s) + ";" for s in self.struct_defs]
        return "STRUCT\n\t" + "\n\t".join(structs_str_list)

    def deepcopy(self, context: Context) -> StructSection:
        struct_defs = [s.deepcopy(context) for s in self.struct_defs]
        new = StructSection(self.loc, struct_defs)

        # Update context
        for struct_def in new.struct_defs:
            context.add_struct(struct_def.symbol, struct_def.members)

        return new

class InputSection(Node):
    def __init__(
        self, loc: log.FileLocation, signal_decls: list[VariableDeclaration]
    ) -> None:
        super().__init__(loc)
        self.signal_decls = signal_decls

    def __str__(self) -> str:
        signals_str_list = [str(s) + ";" for s in self.signal_decls]
        return "INPUT\n\t" + "\n\t".join(signals_str_list)

    def deepcopy(self, context: Context) -> InputSection:
        signal_decls = [s.deepcopy(context) for s in self.signal_decls]
        new = InputSection(self.loc, signal_decls)

        # Update context
        for signal_decl in new.signal_decls:
            for signal in signal_decl.variables:
                context.add_signal(signal, signal_decl.type)

        return new

class DefineSection(Node):
    def __init__(self, loc: log.FileLocation, defines: list[Definition]) -> None:
        super().__init__(loc)
        self.defines = defines

    def __str__(self) -> str:
        defines_str_list = [str(s) + ";" for s in self.defines]
        return "DEFINE\n\t" + "\n\t".join(defines_str_list)

    def deepcopy(self, context: Context) -> DefineSection:
        defines = [d.deepcopy(context) for d in self.defines]
        new = DefineSection(self.loc, defines)

        # Update context
        for define in new.defines:
            context.add_definition(define.symbol, define.expr)

        return new

class SpecSection(Node):
    def __init__(self, loc: log.FileLocation, specs: list[Specification]) -> None:
        super().__init__(loc)
        self.specs = specs

    def deepcopy(self, context: Context) -> SpecSection:
        specs = [cast(Specification, s.deepcopy(context)) for s in self.specs]
        new = type(self)(self.loc, specs)

        # Update context
        for spec in new.specs:
            if isinstance(spec, Formula):
                context.add_formula(spec.symbol, spec)
            elif isinstance(spec, Contract):
                context.add_contract(spec.symbol, spec)

        return new

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

ProgramSection = Union[StructSection, InputSection, DefineSection, SpecSection]

class Program(Node):
    """A Program is a collection of sections that make up a C2PO program."""

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

        self.definitions: list[Definition] = [
            d
            for section in sections
            if isinstance(section, DefineSection)
            for d in section.defines
        ]

        self.total_scq_size = -1
        self.is_dummy = False
        self.is_well_typed = False

    @staticmethod
    def dummy() -> Program:
        """Create a dummy Program for use in commands that require a program but don't have one yet."""
        program = Program(log.FileLocation("<dummy>", 1), [])
        program.is_dummy = True
        return program

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

    def get_max_wpd(self) -> int:
        """Returns the maximum worst-case propagation delay of all specifications in this `Program`."""
        return max([spec.get_expr().wpd for spec in self.get_specs() if isinstance(spec, Formula)])

    def get_spec(self, symbol: str) -> Specification | None:
        for spec in self.ft_spec_set.get_specs():
            if spec.symbol == symbol:
                return spec
        for spec in self.pt_spec_set.get_specs():
            if spec.symbol == symbol:
                return spec
        return None

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

    def postorder_with_definitions(self, context: Context):
        """Performs a postorder traversal of each Definition, FT and PT specification in this `Program`."""
        for definition in self.definitions:
            for expr in postorder(definition.expr, context):
                yield expr

        for expr in self.postorder(context):
            yield expr
        
        for expr in self.preorder(context):
            yield expr

    def pickle(self) -> bytes:
        return pickle.dumps(self)

    def __str__(self) -> str:
        return "\n".join([str(s) for s in self.sections])

    def __repr__(self) -> str:
        return "\n".join([repr(s) for s in self.get_specs()])

    def deepcopy(self, context: Context) -> Program:
        sections = [s.deepcopy(context) for s in self.sections]
        new = Program(self.loc, sections)
        new.total_scq_size = self.total_scq_size
        new.is_dummy = self.is_dummy
        new.is_well_typed = self.is_well_typed
        return new

class Context:
    def __init__(self) -> None:
        self.definitions: dict[str, Expression] = {}
        self.structs: dict[str, dict[str, types.Type]] = {}
        self.signals: dict[str, types.Type] = {}
        self.variables: dict[str, types.Type] = {}
        self.specifications: dict[str, Formula] = {}
        self.contracts: dict[str, Contract] = {}
        self.atomic_id_map: dict[Expression, int] = {}
        self.atomic_expr_map: dict[int, Expression] = {}
        self.bound_vars: dict[str, ArrayExpression] = {}
        self.signal_mapping: types.SignalMapping = {}

        # Trace
        self.trace: list[str] = []

        # Assembly and binary (we attach to context since we need to access it in write_bounds functions)
        self.assembly: list = []
        self.binary: bytes = bytes()

        # R2U2 output string
        self.r2u2_output: str = ""

        # Used in equivalence checking
        self.bounds: list[SymbolicIntervalVariable] = []
        self.constraints: list[Expression] = []

        # Statistics
        self.stats: stats.Stats = stats.Stats()

        # Status flags
        self.is_ft = False
        self.has_future_time = False
        self.has_past_time = False
        self.status = True

        # Globally-accessible options
        self.trace_length: int = -1
        self.mission_time: int = -1
        self.enable_booleanizer: bool = False
        self.script_filename: str = ""
        self.spec_filename: str = ""
        self.trace_filename: str = ""
        self.map_filename: str = ""

        # Paths to executables
        self.egglog_path: Optional[str] = None
        self.smt_solver_path: Optional[str] = None
        self.r2u2_c_path: Optional[str] = None
        self.r2u2_bin_path: Optional[str] = None

    def set_mission_time(self, mission_time: int) -> None:
        """Sets the mission time for the context."""
        self.mission_time = mission_time

    def set_spec_filename(self, filename: str) -> None:
        """Sets the specification filename for the statistics."""
        self.spec_filename = filename
        self.stats.set_spec_filename(filename)

    def clear(self) -> None:
        """
        Clears the context except for the signal mapping and most global options.
        Called when parsing a new program.
        """
        self.definitions.clear()
        self.structs.clear()
        self.signals.clear()
        self.variables.clear()
        self.specifications.clear()
        self.contracts.clear()
        self.atomic_id_map.clear()
        self.atomic_expr_map.clear()
        self.bound_vars.clear()
        self.assembly.clear()
        self.binary = bytes()
        self.bounds.clear()
        self.constraints.clear()
        self.stats = stats.Stats()
        self.trace_length = -1
        self.is_ft = False
        self.has_future_time = False
        self.has_past_time = False
        self.status = True
        self.spec_filename = ""

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

    def deepcopy(self) -> Context:
        """
        Deep copies the context, creating a new context with the same global options and statistics.

        Expressions are not deep copied, keeps the references to the original Expressions in case the program is not copied.
        If the program is to be copied as well, the Expressions will be deep copied in the program.deepcopy() method.
        In that case, use the `deepcopy_program_context()` function.
        """
        new = Context()
        new.definitions = { k: v for k, v in self.definitions.items() }
        new.structs = { k: v for k, v in self.structs.items() }
        new.signals = { k: v for k, v in self.signals.items() }
        new.variables = { k: v for k, v in self.variables.items() }
        new.specifications = { k: v for k, v in self.specifications.items() }
        new.contracts = { k: v for k, v in self.contracts.items() }
        new.atomic_id_map = { k: v for k, v in self.atomic_id_map.items() }
        new.atomic_expr_map = { k: v for k, v in self.atomic_expr_map.items() }
        new.bound_vars = { k: v for k, v in self.bound_vars.items() }
        new.signal_mapping = { k: v for k, v in self.signal_mapping.items() }

        # Deepcopy is not needed for the assembly list
        # TODO: Consider warning user? Or have a check that assembly matches the program?
        new.assembly = self.assembly 

        new.trace = self.trace
        new.binary = self.binary
        new.bounds = [cast(SymbolicIntervalVariable, b.deepcopy(new)) for b in self.bounds]
        new.constraints = [c.deepcopy(new) for c in self.constraints]
        new.stats = self.stats.deepcopy()
        new.trace_length = self.trace_length
        new.is_ft = self.is_ft
        new.has_future_time = self.has_future_time
        new.has_past_time = self.has_past_time
        new.status = self.status
        new.spec_filename = self.spec_filename
        new.trace_filename = self.trace_filename
        new.map_filename = self.map_filename
        new.egglog_path = self.egglog_path
        new.smt_solver_path = self.smt_solver_path
        new.mission_time = self.mission_time
        new.enable_booleanizer = self.enable_booleanizer
        new.script_filename = self.script_filename

        return new

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

def deepcopy_expr(start: Expression, context: Context, memo: dict[int, Expression]) -> Expression:
    """
    Deeply copies an expression `start` using the given context `context` and memo dictionary `memo`.
    Care must be taken to consider the atomic ID mappings when copying expressions.
    If we copy an Atomic, we ensure that the atomic ID mappings are updated to reflect the new expression.
    """
    for expr in postorder(start, context):
        if id(expr) in memo:
            continue

        if isinstance(expr, Atomic):
            new = Atomic(expr.loc, memo[id(expr.get_expr())])

            # Update the atomic ID mappings to reflect the new expression
            atomic_id = context.atomic_id_map[expr]
            context.atomic_id_map[new] = atomic_id
            context.atomic_expr_map[atomic_id] = new
        elif isinstance(expr, Signal):
            new = Signal(expr.loc, expr.symbol, expr.type)
            new.signal_id = expr.signal_id

            # If the Booleanizer is disabled then signals are treated as atomics, so we need to
            # update the atomic ID mappings to reflect the new expression
            if not context.enable_booleanizer and expr in context.atomic_id_map:
                atomic_id = context.atomic_id_map[expr]
                context.atomic_id_map[new] = atomic_id
                context.atomic_expr_map[atomic_id] = new
        elif isinstance(expr, Constant):
            new = Constant(expr.loc, expr.value)
        elif isinstance(expr, MissionTime):
            new = MissionTime(expr.loc)
        elif isinstance(expr, CurrentTimestamp):
            new = CurrentTimestamp(expr.loc)
        elif isinstance(expr, Variable):
            new = Variable(expr.loc, expr.symbol)
        elif isinstance(expr, SymbolicIntervalVariable):
            new = SymbolicIntervalVariable(expr.loc, expr.symbol)
        elif isinstance(expr, ArrayExpression):
            new = ArrayExpression(expr.loc, [memo[id(c)] for c in expr.children])
        elif isinstance(expr, ArrayIndex):
            new = ArrayIndex(expr.loc, memo[id(expr.children[0])], expr.index)
        elif isinstance(expr, Struct):
            new = Struct(expr.loc, expr.symbol, expr.members, [memo[id(c)] for c in expr.children])
        elif isinstance(expr, StructAccess):
            new = StructAccess(expr.loc, memo[id(expr.children[0])], expr.member)
        elif isinstance(expr, FunctionCall):
            new = FunctionCall(expr.loc, expr.symbol, [memo[id(c)] for c in expr.children])
        elif isinstance(expr, Bind):
            new_bound_var = Variable(expr.loc, expr.bound_var.symbol)
            new_set_expr = cast(ArrayExpression, memo[id(expr.set_expr)])
            new = Bind(expr.loc, new_bound_var, new_set_expr)
        elif isinstance(expr, SetAggregation):
            new_bound_var = Variable(expr.loc, expr.bound_var.symbol)
            new_set_expr = cast(ArrayExpression, memo[id(expr.get_set())])
            new_num = memo[id(expr.get_num())] if expr.get_num() else None
            new_expr = memo[id(expr.get_expr())]
            new = SetAggregation(
                expr.loc, expr.operator, new_bound_var, new_set_expr, new_num, new_expr
            )
        elif isinstance(expr, TemporalOperator):
            new_children = [memo[id(c)] for c in expr.children]
            new = TemporalOperator(
                expr.loc,
                expr.operator,
                expr.interval.lb,
                expr.interval.ub,
                new_children,
            )
        elif isinstance(expr, SymbolicTemporalOperator):
            new_children = [memo[id(c)] for c in expr.children]
            new = SymbolicTemporalOperator(
                expr.loc,
                expr.operator,
                expr.interval.lb,
                expr.interval.ub,
                new_children,
            )
        elif isinstance(expr, Operator):
            new = Operator(expr.loc, expr.operator, [memo[id(c)] for c in expr.children], expr.type)
        elif isinstance(expr, Formula):
            new_expr = memo[id(expr.get_expr())]
            new = Formula(expr.loc, expr.symbol, expr.formula_number, new_expr)
        elif isinstance(expr, Contract):
            new_assumption = memo[id(expr.get_assumption())]
            new_guarantee = memo[id(expr.get_guarantee())]
            new = Contract(
                expr.loc,
                expr.symbol,
                expr.formula_numbers[0],
                expr.formula_numbers[1],
                expr.formula_numbers[2],
                new_assumption,
                new_guarantee,
            )
        else:
            raise NotImplementedError(f"deepcopy not implemented for expression type: {type(expr)}")

        expr.copy_attrs(new)
        memo[id(expr)] = new

    return memo[id(start)]

def deepcopy_program_with_context(program: Program, context: Context) -> tuple[Program, Context]:
    new_program = program.deepcopy(context)
    new_context = context.deepcopy()
    return new_program, new_context

def rename(
    target: Expression, repl: Expression, expr: Expression, context: Context
) -> Expression:
    """Traverse `expr` and replace each node equal to `target` with `repl`."""
    # Special case: when expr is target
    if expr == target:
        return repl

    new: Node = expr.deepcopy(context)

    for node in postorder(new, context):
        if target == node:
            node.replace(repl)

    return new

def unroll_temporal_operators(expr: Expression, context: Context) -> Expression:
    """Unrolls the given expression `expr` using the given context `context`"""
    new = expr.deepcopy(context)

    def unrolled_expr(expr: Expression) -> Expression:
        if is_operator(expr, OperatorKind.FUTURE):
            expr = cast(TemporalOperator, expr)
            if expr.interval.lb == expr.interval.ub:
                return expr
            return Operator.LogicalOr(
                expr.loc,
                [
                    TemporalOperator.Future(expr.loc, b, b, expr.children[0])
                    for b in range(expr.interval.lb, expr.interval.ub + 1)
                ],
            )
        elif is_operator(expr, OperatorKind.GLOBAL):
            expr = cast(TemporalOperator, expr)
            if expr.interval.lb == expr.interval.ub:
                return expr
            return Operator.LogicalAnd(
                expr.loc,
                [
                    TemporalOperator.Global(expr.loc, b, b, expr.children[0])
                    for b in range(expr.interval.lb, expr.interval.ub + 1)
                ],
            )
        elif is_operator(expr, OperatorKind.UNTIL):
            expr = cast(TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub

            repl = TemporalOperator.Future(expr.loc, ub, ub, expr.children[1])
            for b in range(ub - 1, lb - 1, -1):
                repl = TemporalOperator.LogicalOr(
                    expr.loc,
                    [
                        TemporalOperator.Future(expr.loc, b, b, expr.children[1]),
                        TemporalOperator.LogicalAnd(
                            expr.loc,
                            [
                                TemporalOperator.Future(expr.loc, b, b, expr.children[0]),
                                repl,
                            ],
                        ),
                    ],
                )

            return repl
        elif is_operator(expr, OperatorKind.RELEASE):
            raise NotImplementedError(
                "Release operator not yet supported for unrolling"
            )

        return expr

    for subexpr in postorder(new, context):
        new = unrolled_expr(subexpr)
        subexpr.replace(new)

    return new

def decompose_intervals(expr: Expression, context: Context) -> Expression:
    """Decomposes temporal operators in `start` to combinations of intervals with sizes that are
    powers of 2. For example: F[2,22] p ==> F[2,2] F[0,15] F[0,3] F[0,1] F[0,1] p."""
    new = expr.deepcopy(context)

    def decompose(expr: Expression) -> Expression:
        if is_operator(expr, OperatorKind.FUTURE):
            expr = cast(TemporalOperator, expr)
            child = expr.children[0]
            lb = expr.interval.lb
            ub = expr.interval.ub

            if lb == ub:
                return expr

            s = ub-lb
            amounts = []
            for n in reversed(range(1, (ub-lb+1).bit_length())):
                while s >= (2**n - 1):
                    amounts.append(2**n - 1)
                    s -= (2**n - 1)
            
            repl = child
            for a in reversed(amounts):
                repl = TemporalOperator.Future(expr.loc, 0, a, repl)

            if lb > 0:
                repl = TemporalOperator.Future(expr.loc, lb, lb, repl)
                
            return repl
        elif is_operator(expr, OperatorKind.GLOBAL):
            expr = cast(TemporalOperator, expr)
            child = expr.children[0]
            lb = expr.interval.lb
            ub = expr.interval.ub
            
            if lb == ub:
                return expr

            s = ub-lb
            amounts = []
            for n in reversed(range(1, (ub-lb+1).bit_length())):
                while s >= (2**n - 1):
                    amounts.append(2**n - 1)
                    s -= (2**n - 1)
            
            repl = child
            for a in reversed(amounts):
                repl = TemporalOperator.Global(expr.loc, 0, a, repl)

            if lb > 0:
                repl = TemporalOperator.Global(expr.loc, lb, lb, repl)
                
            return repl
        elif is_operator(expr, OperatorKind.UNTIL):
            expr = cast(TemporalOperator, expr)
            lhs = expr.children[0]
            rhs = expr.children[1]
            lb = expr.interval.lb
            ub = expr.interval.ub
            
            if lb == ub:
                return expr

            s = ub-lb
            amounts = []
            for n in reversed(range(1, (ub-lb+1).bit_length())):
                while s >= (2**n - 1):
                    amounts.append(2**n - 1)
                    s -= (2**n - 1)
            
            repl = rhs
            for a in reversed(amounts):
                repl = TemporalOperator.Until(expr.loc, 0, a, lhs, repl)

            if lb > 0:
                repl = TemporalOperator.Until(expr.loc, lb, lb, lhs, repl)
                
            return repl

        return expr

    for subexpr in postorder(new, context):
        new = decompose(subexpr)
        subexpr.replace(new)

    return new

def assign_signal_ids(program: Program, context: Context, signal_mapping: types.SignalMapping) -> list[str]:
    """
    Assign signal IDs to the signals in the program.

    Returns:
        A list of signals that were not present in the signal mapping.
    """
    missing_signals = []
    for expr in program.postorder_with_definitions(context):
        if isinstance(expr, Signal):
            if expr.symbol not in signal_mapping:
                missing_signals.append(expr.symbol)
            else:
                expr.signal_id = signal_mapping[expr.symbol]

    return missing_signals

def to_infix_str(start: Expression) -> str:
    s = ""

    stack: list[tuple[int, Expression]] = []
    stack.append((0, start))

    while len(stack) > 0:
        (seen, expr) = stack.pop()

        if isinstance(expr, Constant):
            s += expr.symbol.lower()
        elif isinstance(expr, (CurrentTimestamp, Variable, Signal, SymbolicIntervalVariable, MissionTime, Match)):
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
                s += ", "
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
                s += ", "
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
        elif isinstance(expr, SetAggregation):
            if seen == 0:
                s += f"{expr.symbol}({expr.bound_var} : "
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
                s += f"({expr.symbol} "
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
                s += f" {expr.symbol} "
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
                s += f" {expr.symbol} "
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
        elif isinstance(expr, Atomic):
            stack.append((0, expr.children[0]))
        elif isinstance(expr, Formula):
            if seen == 0:
                if not expr.is_internal_label():
                    s += f"{expr.symbol}: "
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_expr()))
            else:
                s += ";"
        elif isinstance(expr, Contract):
            if seen == 0:
                s += f"{expr.symbol}: "
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_assumption()))
            elif seen == 1:
                s += " => "
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_guarantee()))
            else:
                s += ";"
        else:
            log.internal(f"bad str ({expr})")
            return ""

    return s

def to_prefix_str(start: Expression, with_internal_labels: bool = False) -> str:
    s = ""

    stack: list["tuple[int, Expression]"] = []
    stack.append((0, start))

    while len(stack) > 0:
        (seen, expr) = stack.pop()

        if isinstance(expr, Constant):
            s += expr.symbol.lower() + " "
        elif isinstance(expr, (Constant, CurrentTimestamp, Variable, Signal, SymbolicIntervalVariable, MissionTime, Match)):
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
                s += f"({expr.symbol} "
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[0]))
            else:
                stack.append((seen + 1, expr))
                stack.append((0, expr.children[seen]))
        elif isinstance(expr, SetAggregation):
            if seen == 0:
                s += f"({expr.symbol} ({expr.bound_var} : "
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_set()))
            elif seen == 1:
                s = s[:-1] + ") "
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_expr()))
            else:
                s = s[:-1] + ") "  
        elif isinstance(expr, Operator):
            if seen == 0:
                s += f"({expr.symbol} "
                stack.append((seen + 1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                s = s[:-1] + ") "
        elif isinstance(expr, Atomic):
            stack.append((0, expr.children[0]))
        elif isinstance(expr, Formula):
            if not expr.is_internal_label() or with_internal_labels:
                s += f"{expr.symbol}: "
            stack.append((0, expr.get_expr()))
        elif isinstance(expr, Contract):
            if seen == 0:
                s += f"{expr.symbol}: "
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_assumption()))
            elif seen == 1:
                s += " => "
                stack.append((seen + 1, expr))
                stack.append((0, expr.get_guarantee()))
            else:
                s = s[:-1] + ";"
        elif isinstance(expr, SpecificationSet):
            [stack.append((0, spec)) for spec in reversed(expr.get_specs())]
        else:
            log.internal(f"bad repr ({expr})")
            return ""

    return s[:-1]

def to_mltl_std(program: Program, context: Context) -> str:
    mltl = ""

    stack: list[tuple[int, Expression]] = []

    for spec in program.get_specs():
        if isinstance(spec, Contract):
            log.warning("cannot express AGCs in MLTL standard, skipping")
            continue

        stack.append((0, spec.get_expr()))

        while len(stack) > 0:
            (seen, expr) = stack.pop()

            if isinstance(expr, Constant):
                mltl += expr.symbol.lower() + " "
            elif expr in context.atomic_id_map:
                mltl += f"a{context.atomic_id_map[expr]}"
            elif len(expr.children) == 1 and (
                is_temporal_operator(expr) or is_logical_operator(expr)
            ):
                if seen == 0:
                    mltl += f"({expr.symbol} "
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

                    mltl += f" {symbol} "
                    stack.append((seen + 1, expr))
                    stack.append((0, expr.children[seen]))
            else:
                log.error(
                    f"expression incompatible with MLTL standard ({expr} {type(expr)})"
                )
                return ""

        mltl += "\n"

    return mltl

def is_valid_program(program: Program, context: Context) -> bool:
    return not program.is_dummy

def has_valid_signal_mapping(program: Program, context: Context) -> bool:
    return all(
        (
            expr.symbol in context.signal_mapping
            and expr.signal_id == context.signal_mapping[expr.symbol]
        )
        for expr in program.postorder(context)
        if isinstance(expr, Signal)
    )

def has_atomic_consistent_signal_mapping(program: Program, context: Context) -> bool:
    """
    Returns True if the signal mapping is consistent with the atomic mapping.
    This is only used when the booleanizer is disabled, i.e., signals are directly loaded as atomics.
    In this case, each signal's atomic ID must be the same as its signal ID.    
    """
    if context.enable_booleanizer:
        return True
    return all(
        expr in context.atomic_id_map and context.atomic_id_map[expr] == expr.signal_id
        for expr in program.postorder(context)
        if isinstance(expr, Signal)
    )

def is_well_typed_program(program: Program, context: Context) -> bool:
    return is_valid_program(program, context) and program.is_well_typed

def is_desugared(program: Program, context: Context) -> bool:
    """Returns True if the program is desugared."""
    for expr in program.postorder(context):
        if isinstance(
            expr,
            (
                Struct,
                FunctionCall,
                ArrayExpression,
                StructAccess,
                ArrayIndex,
                SetAggregation,
                Contract,
            ),
        ):
            return False
    return True

def has_valid_scq_sizes(program: Program, context: Context) -> bool:
    """Returns True if the program is SCQ sized. All temporal logic and atomic expressions must have a valid SCQ size."""
    return all(
        expr.scq_size >= 0
        for expr in program.postorder(context)
        if isinstance(expr, Expression)
        and (expr.engine == types.R2U2Engine.TEMPORAL_LOGIC or expr in context.atomic_id_map)
    )

def is_assembled(program: Program, context: Context) -> bool:
    """Returns True if the program is assembled."""
    return len(context.assembly) > 0

def is_only_binary_operators(program: Program, context: Context) -> bool:
    """Returns True if the program contains only binary or unary operators."""
    return all(
        len(expr.children) <= 2 and len(expr.children) >= 0
        for expr in program.postorder(context)
        if isinstance(expr, Expression) and not isinstance(expr, SpecificationSet)
    )

def has_no_extended_operators(program: Program, context: Context) -> bool:
    """Returns True if the program contains no extended operators (xor, ->, F, G, O, H)."""
    return all(
        expr.operator
        not in [
            OperatorKind.LOGICAL_XOR,
            OperatorKind.LOGICAL_IMPLIES,
            OperatorKind.FUTURE,
            OperatorKind.GLOBAL,
            OperatorKind.HISTORICAL,
            OperatorKind.ONCE,
        ]
        for expr in program.postorder(context)
        if isinstance(expr, Operator)
    )

def has_computed_atomics(program: Program, context: Context) -> bool:
    """Returns True if the program contains computed atomics. Computed atomics should be present for all Atomics or, if the booleanizer is disabled, for all Signals."""
    return all(
        expr in context.atomic_id_map
        for expr in program.postorder(context)
        if (isinstance(expr, Atomic)
            or (
                not context.enable_booleanizer
                and isinstance(expr, Signal)
            )
        )
    )
