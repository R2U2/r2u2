"""
A shallow embedding of SMT-LIB 2.
"""
from __future__ import annotations
import enum

from c2po import cpt, types


class BaseSort(enum.Enum):
    BOOL = "Bool"
    INT = "Int"
    REAL = "Real"
    ARRAY = "Array"
    BITVECTOR = "BitVec"


class Sort:
    """
    A shallow embedding of SMT-LIB sorts.
    """
    def __init__(self, base_sort: BaseSort, params: list[Sort] = [], indices: list[int] = []):
        self.base_sort = base_sort
        self.params = params
        self.indices = indices

    @staticmethod
    def Bool() -> Sort:
        return Sort(BaseSort.BOOL)

    @staticmethod
    def Int() -> Sort:
        return Sort(BaseSort.INT)

    @staticmethod
    def Real() -> Sort:
        return Sort(BaseSort.REAL)
    
    @staticmethod
    def Array(element_type: Sort, index_type: Sort) -> Sort:
        return Sort(BaseSort.ARRAY, [element_type, index_type])
    
    @staticmethod
    def BitVector(size: int) -> Sort:
        return Sort(BaseSort.BITVECTOR, [], [size])

    def __str__(self) -> str:
        if len(self.params) == 0 and len(self.indices) == 0:
            return f"({self.base_sort.value})"
        elif len(self.indices) == 0:
            return f"({self.base_sort.value} {' '.join(str(param) for param in self.params)})"
        elif len(self.params) == 0:
            return f"(_ {self.base_sort.value} {' '.join(str(index) for index in self.indices)})"
        else:
            return f"((_ {self.base_sort.value} {' '.join(str(index) for index in self.indices)}) {' '.join(str(param) for param in self.params)})"


def from_cpt_type(cpt_type: types.Type) -> Sort:
    if isinstance(cpt_type, types.BoolType):
        return Sort.Bool()
    elif isinstance(cpt_type, types.IntType):
        return Sort.Int()
    elif isinstance(cpt_type, types.FloatType):
        return Sort.Real()
    elif isinstance(cpt_type, types.ArrayType):
        return Sort.Array(Sort.Int(), from_cpt_type(cpt_type.member_type))
    else:
        raise ValueError(f"Unsupported type: {type(cpt_type)}")


class Term:
    """
    A shallow embedding of SMT-LIB terms.
    """
    def __init__(self, name: str, args: list[Term] = []):
        self.name = name
        self.args = args

    def __str__(self) -> str:
        if len(self.args) == 0:
            return self.name
        else:
            return f"({self.name} {' '.join(str(arg) for arg in self.args)})"
        

def from_cpt_expr(cpt_expr: cpt.Expression, cache: dict[cpt.Expression, Term] = {}) -> Term:
    if cpt_expr in cache:
        return cache[cpt_expr]
    
    if isinstance(cpt_expr, (cpt.Variable, cpt.Constant)):
        term = Term(cpt_expr.symbol)
        cache[cpt_expr] = term
        return term
    elif isinstance(cpt_expr, cpt.Operator):
        term = Term(cpt_expr.symbol, [from_cpt_expr(child, cache) for child in cpt_expr.children])
        cache[cpt_expr] = term
        return term
    else:
        raise ValueError(f"Unsupported term type: {type(cpt_expr)}")


class CommandTypes(enum.Enum):
    SET_LOGIC = "set-logic"
    SET_INFO = "set-info"
    ASSERT = "assert"
    CHECK_SAT = "check-sat"
    GET_VALUE = "get-value"
    DECLARE_FUN = "declare-fun"
    DEFINE_FUN = "define-fun"


class Command:
    def __init__(self, command_type: CommandTypes):
        self.command_type = command_type

    def __str__(self) -> str:
        return self.command_type.value

    def __repr__(self) -> str:
        return self.command_type.value


class SetLogic(Command):
    def __init__(self, logic: str):
        super().__init__(CommandTypes.SET_LOGIC)
        self.logic = logic
    
    def __str__(self) -> str:
        return f"(set-logic {self.logic})"


class SetInfo(Command):
    def __init__(self, info: str):
        super().__init__(CommandTypes.SET_INFO)
        self.info = info

    def __str__(self) -> str:
        return f"(set-info {self.info})"


class DeclareFun(Command):
    def __init__(self, name: str, return_type: Sort, input_types: list[Sort]):
        super().__init__(CommandTypes.DECLARE_FUN)
        self.name = name
        self.return_type = return_type
        self.input_types = input_types

    def __str__(self) -> str:
        return f"(declare-fun {self.name} {self.return_type} ({' '.join(str(input_type) for input_type in self.input_types)}))"


class DefineFun(Command):
    def __init__(self, name: str, return_type: Sort, input_types: list[Sort], body: Term):
        super().__init__(CommandTypes.DEFINE_FUN)
        self.name = name
        self.return_type = return_type
        self.input_types = input_types
        self.body = body

    def __str__(self) -> str:
        return f"(define-fun {self.name} {self.return_type} ({' '.join(str(input_type) for input_type in self.input_types)}) {self.body})"


class Assert(Command):
    def __init__(self, term: Term):
        super().__init__(CommandTypes.ASSERT)
        self.term = term

    def __str__(self) -> str:
        return f"(assert {self.term})"


class CheckSat(Command):
    def __init__(self):
        super().__init__(CommandTypes.CHECK_SAT)

    def __str__(self) -> str:
        return "(check-sat)"


class GetValue(Command):
    def __init__(self, term: Term):
        super().__init__(CommandTypes.GET_VALUE)
        self.term = term    

    def __str__(self) -> str:
        return f"(get-value {self.term})"  


class Program:
    def __init__(self, commands: list[Command] = []):
        self.commands = commands

    def append(self, command: Command) -> None:
        self.commands.append(command)

    def __str__(self) -> str:
        return "\n".join(str(command) for command in self.commands)


class Solver:
    def __init__(self, program: Program):
        self.program = program
