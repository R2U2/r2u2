from __future__ import annotations
from copy import deepcopy
from typing import Any, Dict, Callable, Optional, Set, Union, cast, List, Tuple
import pickle

from .type import *
from c2po.logger import logger

class C2POSection(Enum):
    STRUCT = 0
    INPUT = 1
    DEFINE = 2
    ATOMIC = 3
    FTSPEC = 4
    PTSPEC = 5


class C2PONode():

    def __init__(self, ln: int, c: List[C2PONode]):
        self.ln: int = ln
        self.total_scq_size: int = -1
        self.scq_size: int = -1
        self.symbol: str = ""
        self.bpd: int = 0
        self.wpd: int = 0
        self.type: C2POType = C2PONoType()

        self._children: List[C2PONode] = []
        self._parents: List[C2PONode] = []

        for child in c:
            self._children.append(child)
            child._parents.append(self)

    def get_children(self) -> List[C2PONode]:
        return self._children

    def get_parents(self) -> List[C2PONode]:
        return self._parents

    def get_siblings(self) -> List[C2PONode]:
        siblings = []

        for parent in self.get_parents():
            for sibling in [s for s in parent.get_children()]:
                if sibling in siblings:
                    continue
                if sibling == self:
                    continue
                siblings.append(sibling)
        
        return siblings

    def num_children(self) -> int:
        return len(self._children)

    def num_parents(self) -> int:
        return len(self._parents)

    def get_child(self, i: int) -> C2PONode:
        return self._children[i]

    def get_parent(self, i: int) -> C2PONode:
        return self._parents[i]

    def add_child(self, child: C2PONode):
        self._children.append(child)
        child._parents.append(self)

    def remove_child(self, child: C2PONode):
        self._children.remove(child)
        child._parents.remove(self)

    def replace(self, new: C2PONode):
        """Replaces 'self' with 'new', setting the parents' children of 'self' to 'new'. Note that 'self' is orphaned as a result."""
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

    def __str__(self) -> str:
        return self.symbol

    def to_mltl_std(self) -> str:
        logger.critical(f"{self.ln}: Node type '{type(self)}' unsupported in MLTL standard.")
        return ""

    def copy_attrs(self, new: C2PONode):
        new.scq_size = self.scq_size
        new.symbol = self.symbol
        new.bpd = self.bpd
        new.wpd = self.wpd
        new.type = self.type

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self.get_children()]
        new = type(self)(self.ln, children)
        self.copy_attrs(new)
        return new


class C2POExpression(C2PONode):

    def __init__(self, ln: int, c: List[C2PONode]):
        super().__init__(ln, c)
        self.engine = R2U2Engine.NONE
        self.atomic_id: int = -1 # only set for atomic propositions

    def to_mltl_std(self) -> str:
        if self.atomic_id < 0:
            logger.critical(f"{self.ln}: Non-atomic node type '{type(self)}' unsupported in MLTL standard.")
            return ""
        return f"a{self.atomic_id}"

    def get_children(self) -> List[C2POExpression]:
        return cast(List[C2POExpression], self._children)


class C2POLiteral(C2POExpression):

    def __init__(self, ln: int, a: List[C2PONode]):
        super().__init__(ln,[])

    def __str__(self) -> str:
        return self.symbol


class C2POConstant(C2POLiteral):

    def __init__(self, ln: int, a: List[C2PONode]):
        super().__init__(ln,[])
        self.value = 0

    def get_value(self) -> int|float:
        return self.value


class C2POBool(C2POConstant):

    def __init__(self, ln: int, v: bool):
        super().__init__(ln,[])
        self.type = C2POBoolType(True)
        self.bpd: int = 0
        self.wpd: int = 0
        self.value: bool = v
        self.symbol = str(v)
        self.engine = R2U2Engine.BOOLEANIZER

    def to_mltl_std(self) -> str:
        return self.symbol.lower()
        

class C2POInteger(C2POConstant):

    def __init__(self, ln: int, v: int):
        super().__init__(ln,[])
        self.value: int = v
        self.symbol = str(v)
        self.type = C2POIntType(True)
        self.engine = R2U2Engine.BOOLEANIZER

        if v.bit_length() > C2POIntType.width:
            logger.error(f"{ln} Constant '{v}' not representable in configured int width ('{C2POIntType.width}').")

    def get_value(self) -> int:
        return self.value

    def __deepcopy__(self, memo):
        new = C2POInteger(self.ln, self.value)
        self.copy_attrs(new)
        return new


class C2POFloat(C2POConstant):

    def __init__(self, ln: int, v: float):
        super().__init__(ln,[])
        self.type = C2POFloatType(True)
        self.value: float = v
        self.symbol = str(v)
        self.engine = R2U2Engine.BOOLEANIZER

        # FIXME: 
        # if len(v.hex()[2:]) > FLOAT.width:
        #     logger.error(f"{ln} Constant '{v}' not representable in configured float width ('{FLOAT.width}').")

    def get_value(self) -> float:
        return self.value

    def __deepcopy__(self, memo):
        new = C2POFloat(self.ln, self.value)
        self.copy_attrs(new)
        return new


class C2POVariable(C2POExpression):

    def __init__(self, ln: int, s: str):
        super().__init__(ln, [])
        self.symbol: str = s

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, C2POVariable) and __o.symbol == self.symbol

    def __hash__(self) -> int:
        # note how this compares to __eq__
        # we hash the id so that in sets/dicts different
        # instances of the same variable are distinct
        return id(self)

    def __str__(self) -> str:
        return self.symbol


class C2POSignal(C2POLiteral):

    def __init__(self, ln: int, s: str, t: C2POType):
        super().__init__(ln,[])
        self.symbol: str = s
        self.type: C2POType = t
        self.signal_id: int = -1
        self.engine = R2U2Engine.BOOLEANIZER

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, C2POSignal) and __o.symbol == self.symbol

    def __hash__(self) -> int:
        return id(self)

    def __deepcopy__(self, memo):
        copy = C2POSignal(self.ln, self.symbol, self.type)
        return copy


class C2POAtomicChecker(C2POLiteral):

    def __init__(self, ln: int, s: str):
        super().__init__(ln, [])
        self.symbol: str = s
        self.type: C2POType = C2POBoolType(False)
        self.engine = R2U2Engine.ATOMIC_CHECKER

    def __deepcopy__(self, memo):
        copy = C2POAtomicChecker(self.ln, self.symbol)
        self.copy_attrs(copy)
        return copy


class C2POSet(C2POExpression):

    def __init__(self, ln: int, m: List[C2PONode]):
        super().__init__(ln, m)
        m.sort(key=lambda x: str(x))
        self.max_size: int = len(m)
        self.dynamic_size = None

    def get_max_size(self) -> int:
        return self.max_size

    def get_dynamic_size(self) -> C2PONode | None:
        return self.dynamic_size

    def set_dynamic_size(self, s: C2PONode):
        self.dynamic_size = s

    def __str__(self) -> str:
        s: str = "{"
        for m in self.get_children():
            s += str(m) + ","
        s = s[:-1] + "}"
        return s


class C2POStruct(C2POExpression):

    def __init__(self, ln: int, s: str, m: Dict[str, int], c: List[C2PONode]):
        super().__init__(ln, c)
        self.symbol: str = s

        # hack to get named arguments -- see get_member
        # cannot use *just* members, else the "parent" tracking breaks
        self.members: Dict[str, int] = m 

    def get_member(self, name: str) -> C2PONode:
        return self.get_child(self.members[name])

    def get_members(self) -> Dict[str, int]:
        return self.members

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POStruct(self.ln, self.symbol, self.members, children)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        s = self.symbol + "("
        s += ','.join([f'{i}={self.get_child(e)}' for i,e in self.members.items()])
        s += ")"
        return s


class C2POStructAccess(C2POExpression):

    def __init__(self, ln: int, s: C2PONode, m: str):
        super().__init__(ln, [s])
        self.member: str = m

    def get_struct(self) -> C2POStruct:
        return cast(C2POStruct, self.get_child(0))

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.member)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return str(self.get_struct()) + "." + self.member


class C2POOperator(C2POExpression):

    def __init__(self, ln: int, c: List[C2PONode]):
        super().__init__(ln, c)
        self.arity: int = len(c)


class C2POUnaryOperator(C2POOperator):

    def __init__(self, ln: int, o: List[C2PONode]):
        if len(o) != 1:
            logger.critical(f" '{type(self)}' requires exactly one child node.")
        super().__init__(ln, o)

    def get_operand(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(0))

    def __str__(self) -> str:
        return f"{self.symbol}({self.get_operand()})"


class C2POBinaryOperator(C2POOperator):

    def __init__(self, ln: int, l: List[C2PONode]):
        if len(l) != 2:
            logger.critical(f" '{type(self)}' requires exactly two child nodes.")
        super().__init__(ln, l)

    def get_lhs(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(0))

    def get_rhs(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(1))

    def __str__(self) -> str:
        return f"({self.get_lhs()}){self.symbol}({self.get_rhs()})"


class C2POFunctionCall(C2POOperator):

    def __init__(self, ln: int, s: str, a: List[C2PONode]):
        super().__init__(ln, a)
        self.symbol: str = s

    def __deepcopy__(self, memo):
        return C2POFunctionCall(
            self.ln, 
            self.symbol, 
            deepcopy(cast(List[C2PONode], self.get_children()), 
            memo)
        )

    def __str__(self) -> str:
        s = f"{self.symbol}("
        for arg in self._children:
            s += f"{arg},"
        return s[:-1] + ")"


class C2POSetAggOperator(C2POOperator):

    def __init__(self, ln: int, s: C2POSet, v: C2POVariable,  e: C2PONode):
        super().__init__(ln, [s, v, e])

    def get_set(self) -> C2POSet:
        return cast(C2POSet, self.get_child(0))

    def get_boundvar(self) -> C2POVariable:
        return cast(C2POVariable, self.get_child(1))

    def get_expr(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(2))

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, cast(C2POSet, children[0]), cast(C2POVariable, children[1]), children[2])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return self.symbol + "(" + str(self.get_boundvar()) + ":" + \
            str(self.get_set()) + ")" + "(" + str(self.get_expr()) + ")"


class C2POForEach(C2POSetAggOperator):

    def __init__(self, ln: int, s: C2POSet, v: C2POVariable, e: C2PONode):
        super().__init__(ln, s, v, e)
        self.symbol: str = "foreach"


class C2POForSome(C2POSetAggOperator):

    def __init__(self, ln: int, s: C2POSet, v: C2POVariable, e: C2PONode):
        super().__init__(ln, s, v, e)
        self.symbol: str = "forsome"


class C2POForExactly(C2POSetAggOperator):

    def __init__(self, ln: int, s: C2POSet, n: C2PONode, v: C2POVariable, e: C2PONode):
        super().__init__(ln, s, v, e)
        self.symbol: str = "forexactly"
        self.add_child(n)

    def get_num(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(3))
    
    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POForExactly(self.ln, cast(C2POSet, children[0]), children[3], cast(C2POVariable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class C2POForAtLeast(C2POSetAggOperator):

    def __init__(self, ln: int, s: C2POSet, n: C2PONode, v: C2POVariable, e: C2PONode):
        super().__init__(ln, s, v, e)
        self.symbol: str = "foratleast"
        self.add_child(n)

    def get_num(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(3))

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POForExactly(self.ln, cast(C2POSet, children[0]), children[3], cast(C2POVariable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class C2POForAtMost(C2POSetAggOperator):

    def __init__(self, ln: int, s: C2POSet, n: C2PONode, v: C2POVariable, e: C2PONode):
        super().__init__(ln, s, v, e)
        self.symbol: str = "foratmost"
        self.add_child(n)

    def get_num(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(3))

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POForExactly(self.ln, cast(C2POSet, children[0]), children[3], cast(C2POVariable, children[1]), children[2])
        self.copy_attrs(new)
        return new


class Count(C2POOperator):

    def __init__(self, ln: int, n: C2PONode, c: List[C2PONode]):
        # Note: all members of c must be of type Boolean
        super().__init__(ln, c)
        self.num: C2PONode = n
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


class C2POBitwiseOperator(C2POOperator):

    def __init__(self, ln: int, c: List[C2PONode]):
        super().__init__(ln, c)
        self.engine = R2U2Engine.BOOLEANIZER


class C2POBitwiseAnd(C2POBitwiseOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "&"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POBitwiseAnd(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POBitwiseOr(C2POBitwiseOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "|"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POBitwiseOr(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POBitwiseXor(C2POBitwiseOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "^"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POBitwiseXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POBitwiseShiftLeft(C2POBitwiseOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "<<"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POBitwiseShiftLeft(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POBitwiseShiftRight(C2POBitwiseOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = ">>"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POBitwiseShiftRight(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POBitwiseNegate(C2POBitwiseOperator, C2POUnaryOperator):

    def __init__(self, ln: int, o: C2PONode):
        super().__init__(ln, [o])
        self.symbol = "~"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POBitwiseNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new


class C2POArithmeticOperator(C2POOperator):

    def __init__(self, ln: int, c: List[C2PONode]):
        super().__init__(ln, c)
        self.engine = R2U2Engine.BOOLEANIZER

    def __str__(self) -> str:
        s = f"{self.get_child(0)}"
        for c in range(1,len(self._children)):
            s += f"{self.symbol}{self.get_child(c)}"
        return s


class C2POArithmeticAdd(C2POArithmeticOperator):

    def __init__(self, ln: int, c: List[C2PONode]):
        # force binary operator for now
        if len(c) > 2:
            prev = C2POArithmeticAdd(ln, c[0:2])
            for i in range(2,len(c)-1):
                prev = C2POArithmeticAdd(ln, [prev,c[i]])
            super().__init__(ln, [prev,c[len(c)-1]])
            self.type = c[0].type
        else:
            super().__init__(ln, c)
            self.type = c[0].type

        self.symbol = "+"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POArithmeticAdd(self.ln, children)
        self.copy_attrs(new)
        return new


class C2POArithmeticSubtract(C2POArithmeticOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "-"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POArithmeticSubtract(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POArithmeticMultiply(C2POArithmeticOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "*"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POArithmeticMultiply(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POArithmeticDivide(C2POArithmeticOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "/"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POArithmeticDivide(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POArithmeticModulo(C2POArithmeticOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "%"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POArithmeticModulo(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POArithmeticNegate(C2POUnaryOperator, C2POArithmeticOperator):

    def __init__(self, ln: int, o: C2PONode):
        super().__init__(ln, [o])
        self.symbol = "-"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POArithmeticNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new


class C2PORelationalOperator(C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.engine = R2U2Engine.BOOLEANIZER

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POEqual(C2PORelationalOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, lhs, rhs)
        self.symbol = "=="


class C2PONotEqual(C2PORelationalOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, lhs, rhs)
        self.symbol = "!="


class C2POGreaterThan(C2PORelationalOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, lhs, rhs)
        self.symbol = ">"


class C2POLessThan(C2PORelationalOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, lhs, rhs)
        self.symbol = "<"


class C2POGreaterThanOrEqual(C2PORelationalOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, lhs, rhs)
        self.symbol = ">="


class C2POLessThanOrEqual(C2PORelationalOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, lhs, rhs)
        self.symbol = "<="


class C2POLogicalOperator(C2POOperator):

    def __init__(self, ln: int, c: List[C2PONode]):
        super().__init__(ln, c)
        self.bpd = min([child.bpd for child in c])
        self.wpd = max([child.wpd for child in c])
        self.engine = R2U2Engine.TEMPORAL_LOGIC


class C2POLogicalOr(C2POLogicalOperator):

    def __init__(self, ln: int, c: List[C2PONode]):
        # force binary operator for now
        if len(c) > 2:
            prev = C2POLogicalOr(ln, c[0:2])
            for i in range(2,len(c)-1):
                prev = C2POLogicalOr(ln, [prev,c[i]])
            super().__init__(ln, [prev,c[len(c)-1]])
        else:
            super().__init__(ln, c)

        super().__init__(ln, c)
        self.symbol = "||"

    def __str__(self) -> str:
        return self.symbol.join([str(c) for c in self.get_children()])

    def to_mltl_std(self) -> str:
        return "|".join([f"({c.to_mltl_std()})" for c in self.get_children()])


class C2POLogicalAnd(C2POLogicalOperator):

    def __init__(self, ln: int, c: List[C2PONode]):
        # force binary operator for now
        if len(c) > 2:
            prev = C2POLogicalAnd(ln, c[0:2])
            for i in range(2,len(c)-1):
                prev = C2POLogicalAnd(ln, [prev,c[i]])
            super().__init__(ln, [prev,c[len(c)-1]])
        else:
            super().__init__(ln, c)

        self.symbol = "&&"

    def __str__(self) -> str:
        return self.symbol.join([str(c) for c in self.get_children()])

    def to_mltl_std(self) -> str:
        return "&".join([f"({c.to_mltl_std()})" for c in self.get_children()])


class C2POLogicalXor(C2POLogicalOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "^^"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POLogicalXor(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new


class C2POLogicalImplies(C2POLogicalOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "->"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POLogicalImplies(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()})->({self.get_rhs().to_mltl_std()})"


class C2POLogicalIff(C2POLogicalOperator, C2POBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode):
        super().__init__(ln, [lhs, rhs])
        self.symbol = "<->"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POLogicalIff(self.ln, children[0], children[1])
        self.copy_attrs(new)
        return new

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()})<->({self.get_rhs().to_mltl_std()})"


class C2POLogicalNegate(C2POLogicalOperator, C2POUnaryOperator):

    def __init__(self, ln: int, o: C2PONode):
        super().__init__(ln, [o])
        self.symbol = "!"

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POLogicalNegate(self.ln, children[0])
        self.copy_attrs(new)
        return new

    def to_mltl_std(self) -> str:
        return f"!({self.get_operand().to_mltl_std()})"


class C2POTemporalOperator(C2POOperator):

    def __init__(self, ln: int, c: List[C2PONode], l: int, u: int):
        super().__init__(ln, c)
        self.interval = Interval(lb=l,ub=u)
        self.engine = R2U2Engine.TEMPORAL_LOGIC


class C2POFutureTimeOperator(C2POTemporalOperator):

    def __init__(self, ln: int, c: List[C2PONode], l: int, u: int):
        super().__init__(ln, c, l, u)


class C2POPastTimeOperator(C2POTemporalOperator):

    def __init__(self, ln: int, c: List[C2PONode], l: int, u: int):
        super().__init__(ln, c, l, u)


# cannot inherit from BinaryOperator due to multiple inheriting classes
# with different __init__ signatures
class C2POFutureTimeBinaryOperator(C2POTemporalOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode, l: int, u: int):
        super().__init__(ln, [lhs, rhs], l, u)
        self.bpd = min(lhs.bpd, rhs.bpd) + self.interval.lb
        self.wpd = max(lhs.wpd, rhs.wpd) + self.interval.ub

    def get_lhs(self) -> C2PONode:
        return self.get_child(0)

    def get_rhs(self) -> C2PONode:
        return self.get_child(1)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.get_lhs()!s}){self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()}){self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_rhs().to_mltl_std()})"


class C2POUntil(C2POFutureTimeBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode, l: int, u: int):
        super().__init__(ln, lhs, rhs, l, u)
        self.symbol = "U"


class C2PORelease(C2POFutureTimeBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode, l: int, u: int):
        super().__init__(ln, lhs, rhs, l, u)
        self.symbol = "R"


class C2POFutureTimeUnaryOperator(C2POFutureTimeOperator):

    def __init__(self, ln: int, o: C2PONode, l: int, u: int):
        super().__init__(ln, [o], l, u)
        self.bpd = o.bpd + self.interval.lb
        self.wpd = o.wpd + self.interval.ub

    def get_operand(self) -> C2PONode:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"

    def to_mltl_std(self) -> str:
        return f"{self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_operand().to_mltl_std()})"


class C2POGlobal(C2POFutureTimeUnaryOperator):

    def __init__(self, ln: int, o: C2PONode, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.symbol = "G"


class C2POFuture(C2POFutureTimeUnaryOperator):

    def __init__(self, ln: int, o: C2PONode, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.symbol = "F"


class C2POPastTimeBinaryOperator(C2POPastTimeOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode, l: int, u: int):
        super().__init__(ln, [lhs, rhs], l, u)

    def get_lhs(self) -> C2PONode:
        return self.get_child(0)

    def get_rhs(self) -> C2PONode:
        return self.get_child(1)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], children[1], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"({self.get_lhs()!s}){self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_rhs()!s})"

    def to_mltl_std(self) -> str:
        return f"({self.get_lhs().to_mltl_std()}){self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_rhs().to_mltl_std()})"


class C2POSince(C2POPastTimeBinaryOperator):

    def __init__(self, ln: int, lhs: C2PONode, rhs: C2PONode, l: int, u: int):
        super().__init__(ln, lhs, rhs, l, u)
        self.symbol = "S"


class C2POPastTimeUnaryOperator(C2POPastTimeOperator):

    def __init__(self, ln: int, o: C2PONode, l: int, u: int):
        super().__init__(ln, [o], l, u)

    def get_operand(self) -> C2PONode:
        return self.get_child(0)

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = type(self)(self.ln, children[0], self.interval.lb, self.interval.ub)
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return f"{self.symbol!s}[{self.interval.lb},{self.interval.ub}]({self.get_operand()!s})"

    def to_mltl_std(self) -> str:
        return f"{self.symbol}[{self.interval.lb},{self.interval.ub}]({self.get_operand().to_mltl_std()})"


class C2POHistorical(C2POPastTimeUnaryOperator):

    def __init__(self, ln: int, o: C2PONode, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.symbol = "H"


class C2POOnce(C2POPastTimeUnaryOperator):

    def __init__(self, ln: int, o: C2PONode, l: int, u: int):
        super().__init__(ln, o, l, u)
        self.symbol = "O"


class C2POSpecification(C2POExpression):

    def __init__(self, ln: int, lbl: str, f: int, e: C2PONode):
        super().__init__(ln, [e])
        self.symbol: str = lbl
        self.formula_number: int = f
        self.engine = R2U2Engine.TEMPORAL_LOGIC

    def get_expr(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(0))

    def __deepcopy__(self, memo):
        children = [deepcopy(c, memo) for c in self._children]
        new = C2POSpecification(self.ln, self.symbol, self.formula_number, children[0])
        self.copy_attrs(new)
        return new

    def __str__(self) -> str:
        return (str(self.formula_number) if self.symbol == "" else self.symbol) + ": " + str(self.get_expr())

    def to_mltl_std(self) -> str:
        return self.get_expr().to_mltl_std()


class C2POContract(C2PONode):

    def __init__(
        self, 
        ln: int, 
        lbl: str, 
        f1: int, 
        f2: int, 
        f3: int, 
        a: C2POExpression, 
        g: C2POExpression
    ):
        super().__init__(ln, [a, g])
        self.symbol: str = lbl
        self.formula_numbers: Tuple[int,int,int] = (f1,f2,f3)

    def get_assumption(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(0))

    def get_guarantee(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(1))

    def __str__(self) -> str:
        return f"({self.get_assumption()})=>({self.get_guarantee()})"


class C2POStructDefinition(C2PONode):

    def __init__(self, ln: int, symbol: str, m: List[C2PONode]):
        super().__init__(ln, m)
        self.symbol = symbol
        self._members = {}
        for decl in cast(List[C2POVariableDeclaration], m):
            for sym in decl.get_symbols():
                self._members[sym] = decl.get_type()

    def get_declarations(self) -> List[C2POVariableDeclaration]:
        return cast(List[C2POVariableDeclaration], self._children)

    def get_members(self) -> Dict[str, C2POType]:
        return self._members

    def __str__(self) -> str:
        members_str_list = [str(s)+";" for s in self._children]
        return self.symbol + "{" + " ".join(members_str_list) + ")"


class C2POVariableDeclaration(C2PONode):

    def __init__(self, ln: int, vars: List[str], t: C2POType):
        super().__init__(ln, [])
        self._variables = vars
        self._type = t

    def get_symbols(self) -> List[str]:
        return self._variables

    def get_type(self) -> C2POType:
        return self._type

    def __str__(self) -> str:
        return f"{','.join(self._variables)}: {str(self._type)}"


class C2PODefinition(C2PONode):

    def __init__(self, ln: int, symbol: str, e: C2POExpression):
        super().__init__(ln, [e])
        self.symbol = symbol

    def get_expr(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(0))

    def __str__(self) -> str:
        return f"{self.symbol} := {self.get_expr()}"


class C2POAtomicCheckerDefinition(C2PONode):

    def __init__(self, ln: int, symbol: str, e: C2POExpression):
        super().__init__(ln, [e])
        self.symbol = symbol

    def get_expr(self) -> C2POExpression:
        return cast(C2POExpression, self.get_child(0))

    def __str__(self) -> str:
        return f"{self.symbol} := {self.get_expr()}"


class C2POStructSection(C2PONode):

    def __init__(self, ln: int, struct_defs: List[C2PONode]):
        super().__init__(ln, struct_defs)

    def get_structs(self) -> List[C2POStructDefinition]:
        return cast(List[C2POStructDefinition], self._children)

    def replace(self, node: C2PONode):
        logger.critical(f"Attempting to replace a C2POStructSection.")

    def __str__(self) -> str:
        structs_str_list = [str(s)+";" for s in self._children]
        return "STRUCT\n\t" + "\n\t".join(structs_str_list)


class C2POInputSection(C2PONode):

    def __init__(self, ln: int, signal_decls: List[C2PONode]):
        super().__init__(ln, signal_decls)

    def get_signals(self) -> List[C2POVariableDeclaration]:
        return cast(List[C2POVariableDeclaration], self._children)

    def replace(self, node: C2PONode):
        logger.critical(f"Attempting to replace a C2POInputSection.")

    def __str__(self) -> str:
        signals_str_list = [str(s)+";" for s in self._children]
        return "INPUT\n\t" + "\n\t".join(signals_str_list)


class C2PODefineSection(C2PONode):

    def __init__(self, ln: int, defines: List[C2PONode]):
        super().__init__(ln, defines)

    def get_definitions(self) -> List[C2PODefinition]:
        return cast(List[C2PODefinition], self._children)

    def replace(self, node: C2PONode):
        logger.critical(f"Attempting to replace a C2PODefineSection.")

    def __str__(self) -> str:
        defines_str_list = [str(s)+";" for s in self._children]
        return "DEFINE\n\t" + "\n\t".join(defines_str_list)


class C2POAtomicSection(C2PONode):

    def __init__(self, ln: int, atomics: List[C2PONode]):
        super().__init__(ln, atomics)

    def get_atomic_checkers(self) -> List[C2POAtomicCheckerDefinition]:
        return cast(List[C2POAtomicCheckerDefinition], self._children)

    def replace(self, node: C2PONode):
        logger.critical(f"Attempting to replace a C2POAtomicSection.")

    def __str__(self) -> str:
        atomics_str_list = [str(s)+";" for s in self._children]
        return "ATOMIC\n\t" + "\n\t".join(atomics_str_list)


class C2POSpecSection(C2PONode):

    def __init__(self, ln: int, s: List[C2PONode]):
        super().__init__(ln, s)

    def get_specs(self) -> List[Union[C2POSpecification, C2POContract]]:
        return cast(List[Union[C2POSpecification, C2POContract]], self._children)

    def replace(self, node: C2PONode):
        logger.critical(f"Attempting to replace a C2POSpecSection.")

    def __str__(self) -> str:
        spec_str_list = [str(s)+";" for s in self._children]
        return "\n\t".join(spec_str_list)

    def to_mltl_std(self) -> str:
        return "\n".join([s.to_mltl_std() for s in self.get_specs()])


class C2POFutureTimeSpecSection(C2POSpecSection):

    def __init__(self, ln: int, s: List[C2PONode]):
        super().__init__(ln, s)

    def __str__(self) -> str:
        return "FTPSEC\n\t" + super().__str__()


class C2POPastTimeSpecSection(C2POSpecSection):

    def __init__(self, ln: int, s: List[C2PONode]):
        super().__init__(ln, s)

    def __str__(self) -> str:
        return "PTSPEC\n\t" + super().__str__()


class C2POProgram(C2PONode):

    def __init__(self, ln: int, sections: List[C2PONode]):
        super().__init__(ln, sections)

        self.future_time_spec_section_idx = -1
        self.past_time_spec_section_idx = -1

        for section in sections:
            if isinstance(section, C2POFutureTimeSpecSection):
                self.future_time_spec_section_idx = sections.index(section)
            elif isinstance(section, C2POPastTimeSpecSection):
                self.past_time_spec_section_idx = sections.index(section)

        # Data
        self.timestamp_width: int = 0

        # Computable properties
        self.cpu_wcet: int = -1
        self.fpga_wcet: float = -1

        # Do we need/want these?
        # Predicates
        self.is_type_correct: bool = False
        self.is_set_agg_free: bool = False
        self.is_struct_access_free: bool = False
        self.is_cse_reduced: bool = False

    # def is_pure_mltl(self) -> bool:
    #     """Return true if each expression in the specification set if pure MLTL. If so, the program can be dumped in the MLTL standard format."""
    #     mltl = True

    #     def is_pure_mltl_util(node: C2PONode):
    #         nonlocal mltl
    #         if not (isinstance(node, C2POSignal) or isinstance(node, C2POBool) or isinstance(node, C2POLogicalOperator) or isinstance(node, C2POTemporalOperator)):
    #             mltl = False

    #     [postorder(expr, is_pure_mltl_util) for expr in self.get_specs()]

    #     return mltl

    def get_sections(self) -> List[C2POSection]:
        return cast(List[C2POSection], self._children)

    def get_spec_sections(self) -> List[C2POSpecSection]:
        return [s for s in self._children if isinstance(s, C2POSpecSection)]

    def get_future_time_spec_section(self) -> Optional[C2POFutureTimeSpecSection]:
        if self.future_time_spec_section_idx < 0:
            return None
        return cast(
            C2POFutureTimeSpecSection, 
            self.get_child(self.future_time_spec_section_idx)
        ) 

    def get_past_time_spec_section(self) -> Optional[C2POPastTimeSpecSection]:
        if self.past_time_spec_section_idx < 0:
            return None
        return cast(
            C2POPastTimeSpecSection, 
            self.get_child(self.past_time_spec_section_idx)
        ) 

    def get_future_time_specs(self) -> List[Union[C2POSpecification, C2POContract]]:
        future_time_spec_section = self.get_future_time_spec_section()
        if future_time_spec_section:
            return future_time_spec_section.get_specs()
        return []

    def get_past_time_specs(self) -> List[Union[C2POSpecification, C2POContract]]:
        past_time_spec_section = self.get_past_time_spec_section()
        if past_time_spec_section:
            return past_time_spec_section.get_specs()
        return []

    def get_specs(self) -> List[Union[C2POSpecification, C2POContract]]:
        return self.get_future_time_specs() + self.get_past_time_specs()

    def replace(self, node: C2PONode):
        logger.critical(f"Attempting to replace a program.")

    def pickle(self) -> bytes:
        return pickle.dumps(self)

    def __str__(self) -> str:
        return "\n".join([str(s) for s  in self.get_children()])

    def to_mltl_std(self) -> str:
        return "\n".join([s.to_mltl_std() for s in self.get_specs()]) + "\n"


class C2POContext():

    def __init__(
        self, 
        impl: R2U2Implementation, 
        mission_time: int,
        atomic_checkers: bool, 
        booleanizer: bool,
        assembly_enabled: bool,
        signal_mapping: SignalMapping
    ):
        self.definitions: Dict[str, C2POExpression] = {}
        self.structs: Dict[str, Dict[str, C2POType]] = {}
        self.signals: Dict[str, C2POType] = {}
        self.variables: Dict[str, C2POType] = {}
        self.atomic_checkers: Dict[str, C2POExpression] = {}
        self.specifications: Dict[str, C2POSpecification] = {}
        self.contracts: Dict[str, C2POContract] = {}
        self.atomics: Set[C2POExpression] = set()
        self.implementation = impl
        self.booleanizer_enabled = booleanizer
        self.atomic_checker_enabled = atomic_checkers
        self.mission_time = mission_time
        self.signal_mapping = signal_mapping
        self.assembly_enabled = assembly_enabled

        self.is_ft = False
        self.has_future_time = False
        self.has_past_time = False

        self.atomic_checker_filters: Dict[str, List[C2POType]] = {
            "rate": [C2POFloatType(False)],
            "movavg": [C2POFloatType(False), C2POIntType(True)],
            "abs_diff_angle": [C2POFloatType(False), C2POFloatType(True)],
            "exactly_one_of": [C2POSetType(False, C2POBoolType(False))],
            "all_of": [C2POSetType(False, C2POBoolType(False))],
            "none_of": [C2POSetType(False, C2POBoolType(False))]
        }

    def get_symbols(self) -> List[str]:
        symbols =  [s for s in self.definitions.keys()]
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

    def set_future_time(self):
        self.is_ft = True

    def set_past_time(self):
        self.is_ft = False

    def add_signal(self, symbol: str, t: C2POType):
        self.signals[symbol] = t
        self.variables[symbol] = t

    def add_variable(self, symbol: str, t: C2POType):
        self.variables[symbol] = t

    def add_definition(self, symbol: str, e: C2POExpression):
        self.definitions[symbol] = e

    def add_struct(self, symbol: str, m: Dict[str, C2POType]):
        self.structs[symbol] = m

    def add_atomic(self, symbol: str, e: C2POExpression):
        self.atomic_checkers[symbol] = e

    def add_specification(self, symbol, s: C2POSpecification):
        self.specifications[symbol] = s

    def add_contract(self, symbol, c: C2POContract):
        self.contracts[symbol] = c

    def remove_variable(self, symbol):
        del self.variables[symbol]
    

def postorder(node: C2PONode, func: Callable[[C2PONode], Any]):
    """Perform an iterative postorder traversal of node, calling func on each node."""
    stack: List[Tuple[bool, C2PONode]] = [(False, node)]
    visited: Set[int] = set()

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


def preorder(node: C2PONode, func: Callable[[C2PONode], Any]):
    """Perform an iterative preorder traversal of a, calling func on each node. func must not alter the children of its argument node."""
    stack: List[C2PONode] = [node]

    while len(stack) > 0:
        c = stack.pop()
        func(c)

        for child in reversed(c.get_children()):
            stack.append(child)


def rename(v: C2PONode, repl: C2PONode, expr: C2PONode) -> C2PONode:
    """Traverse expr and replace each node equal to v with repl."""
    # Special case: when expr is v
    if expr == v:
        return repl

    new: C2PONode = deepcopy(expr)

    def rename_util(a: C2PONode):
        if v == a:
            a.replace(repl)

    postorder(new, rename_util)
    return new
