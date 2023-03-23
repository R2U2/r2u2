from argparse import PARSER
from os import chdir
import re
from logging import getLogger
from time import perf_counter
from tkinter.tix import Form

from requests import post

from .logger import *
from .ast import *
from .parser import C2POLexer
from .parser import C2POParser


logger = getLogger(COLOR_LOGGER_NAME)


class R2U2Implementation(Enum):
    C = 0
    CPP = 1
    VHDL = 2


def str_to_r2u2_implementation(s: str) -> R2U2Implementation:
    if s.lower() == 'c':
        return R2U2Implementation.C
    elif s.lower() == 'c++' or s.lower() == 'cpp':
        return R2U2Implementation.CPP
    elif s.lower() == 'fpga' or s.lower() == 'vhdl':
        return R2U2Implementation.VHDL
    else:
        logger.error(f' R2U2 implementation \'{s}\' unsupported. Defaulting to C.')
        return R2U2Implementation.C


class ReturnCode(Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERROR = 2
    TYPE_CHECK_ERROR = 3
    ASM_ERROR = 4
    ENGINE_SELECT_ERROR = 5


instruction_list = [cls for (name,cls) in inspect.getmembers(sys.modules['compiler.ast'], 
        lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction))]

default_cpu_latency_table: dict[str, int] = { name:10 for (name,value) in 
    inspect.getmembers(sys.modules['compiler.ast'], 
        lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction) and 
            obj != Instruction and 
            obj != TLInstruction and 
            obj != BZInstruction) }

default_fpga_latency_table: dict[str, tuple[float,float]] = { name:(10.0,10.0) for (name,value) in 
    inspect.getmembers(sys.modules['compiler.ast'], 
        lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction) and 
            obj != Instruction and 
            obj != TLInstruction and 
            obj != BZInstruction) }


at_filter_table: dict[str, tuple[Type, list[Type]]] = {
    "rate": (FLOAT(), [FLOAT()])
}


def type_check(program: Program, at: bool, bz: bool, st: StructDict) -> bool:
    """
    Performs type checking of the argument program. Uses type inferences to assign correct types to each 
    AST node in the program and returns whether the program is properly type checked.

    Preconditions: 
        - None

    Postconditions: 
        - program is type correct
        - All descendants of program have a valid Type (i.e., none are NOTYPE)
    """
    status: bool = True
    explored: list[AST] = []
    context: dict[str,Type] = {}
    formula_type: FormulaType = FormulaType.PROP

    def type_check_util(a: AST) -> None:
        nonlocal status

        if a in explored:
            return
        explored.append(a)

        if isinstance(a,Signal) or isinstance(a,Constant):
            return
        elif isinstance(a,Program):
            for c in a.get_children():
                type_check_util(c)
        elif isinstance(a,Specification):
            child = a.get_expr()
            type_check_util(child)

            if not child.type == BOOL():
                status = False
                logger.error(f'{a.ln}: Specification must be of boolean type (found \'{child.type}\')\n\t{a}')
        elif isinstance(a,RelationalOperator):
            lhs = a.get_lhs()
            rhs = a.get_rhs()
            type_check_util(lhs)
            type_check_util(rhs)

            if isinstance(a,Equal) or isinstance(a,NotEqual):
                if not is_integer_type(lhs.type) or not is_integer_type(rhs.type):
                    status = False
                    logger.error(f'{a.ln}: Invalid operands for \'{a.name}\', must be of integer type (found \'{lhs.type}\' and \'{rhs.type}\')\n\t{a}')

            if lhs.type != rhs.type:
                status = False
                logger.error(f'{a.ln}: Invalid operands for \'{a.name}\', must be of same type (found \'{lhs.type}\' and \'{rhs.type}\')\n\t{a}')

            if at: # AT checkers restrict the usage of comparison operators
                if not isinstance(lhs, Signal) and not isinstance(lhs, Function):
                    status = False
                    logger.error(f'{a.ln}: Left-hand argument for AT checker must be signal or filter (found {lhs}\n\t{a}')
                if not isinstance(rhs, Literal):
                    status = False
                    logger.error(f'{a.ln}: Right-hand argument for AT checker must be signal or constant (found {rhs}\n\t{a}')

            a.type = BOOL()
        elif isinstance(a, Function):
            if not at: 
                status = False
                logger.error(f'{a.ln}: Found AT expression, but AT expressions disabled\n\t{a}')
            
            if a.name in at_filter_table:
                if len(at_filter_table[a.name][1]) == len(a.get_children()):
                    for i in range(0, len(a.get_children())):
                        type_check_util(a.get_child(i))
                        if at_filter_table[a.name][1][i] != a.get_child(i).type:
                            status = False
                            logger.error(f'{a.ln}: AT filter argument {i} mismatch (found {a.get_child(i).type}, expected {at_filter_table[a.name][1][i]}\n\t{a}')
                    if status:
                        a.type = at_filter_table[a.name][0]
                else:
                    status = False
                    logger.error(f"{a.ln}: AT filter {a.name} argument number mismatch (found {len(a.get_children())}, expected {len(at_filter_table[a.name])})\n\t{a}")
            else:
                status = False
                logger.error(f'{a.ln}: AT filter {a.name} not supported.\n\t{a}')

        elif isinstance(a, ArithmeticOperator):
            if not bz:
                status = False
                logger.error(f'{a.ln}: Found BZ expression, but Booleanizer expressions disabled\n\t{a}')

            for c in a.get_children():
                type_check_util(c)
            t: Type = a.get_child(0).type

            if isinstance(a, ArithmeticDivide):
                rhs: AST = a.get_rhs()
                if isinstance(rhs, Constant) and rhs.get_value() == 0:
                    status = False
                    logger.error(f'{a.ln}: Divide by zero\n\t{a}')

            for c in a.get_children():
                if c.type != t:
                    status = False
                    logger.error(f'{a.ln}: Operand of \'{a}\' must be of homogeneous type (found \'{c.type}\' and \'{t}\')')

            a.type = t
        elif isinstance(a, BitwiseOperator):
            status = False
            logger.error(f'{a.ln}: Bitwise operators unsupported.\n\t{a}')
        elif isinstance(a, LogicalOperator):
            for c in a.get_children():
                type_check_util(c)
                if c.type != BOOL():
                    status = False
                    logger.error(f'{a.ln}: Invalid operands for \'{a.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{a}')

            a.type = BOOL()
        elif isinstance(a, TemporalOperator):
            for c in a.get_children():
                type_check_util(c)
                if c.type != BOOL():
                    status = False
                    logger.error(f'{a.ln}: Invalid operands for \'{a.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{a}')

            if a.interval.lb > a.interval.ub:
                status = status
                logger.error(f'{a.ln}: Time interval invalid, lower bound must less than or equal to upper bound (found [{a.interval.lb},{a.interval.ub}])')

            a.type = BOOL()
        elif isinstance(a,Set):
            t: Type = NOTYPE()
            for m in a.get_children():
                type_check_util(m)
                t = m.type

            for m in a.get_children():
                if m.type != t:
                    status = False
                    logger.error(f'{a.ln}: Set \'{a}\' must be of homogeneous type (found \'{m.type}\' and \'{t}\')')

            a.type = SET(t)
        elif isinstance(a,Variable):
            if a.name in context.keys():
                a.type = context[a.name]
            else:
                status = False
                logger.error(f'{a.ln}: Variable \'{a}\' not recognized')
        elif isinstance(a,SetAggOperator):
            s: Set = a.get_set()
            boundvar: Variable = a.get_boundvar()

            type_check_util(s)

            if isinstance(s.type, SET):
                context[boundvar.name] = s.type.member_type
            else:
                status = False
                logger.error(f'{a.ln}: Set aggregation set must be Set type (found \'{s.type}\')')

            if isinstance(a, ForExactlyN) or isinstance(a, ForAtLeastN) or isinstance(a, ForAtMostN):
                n: AST = a.num
                type_check_util(n)
                if not is_integer_type(n.type):
                    status = False
                    logger.error(f'{a.ln}: Parameter for set aggregation must be integer type (found \'{n.type}\')')

            expr: AST = a.get_expr()
            type_check_util(expr)

            if expr.type != BOOL():
                status = False
                logger.error(f'{a.ln}: Set aggregation argument must be Boolean (found \'{expr.type}\')')

            del context[boundvar.name]
            explored.remove(boundvar)
            a.type = BOOL()
        elif isinstance(a,Struct):
            for name,member in a.get_members().items():
                type_check_util(member)
                if st[a.name][name] != member.type:
                    logger.error(f'{a.ln}: Member \'{name}\' invalid type for struct \'{a.name}\' (expected \'{st[a.name][name]}\' but got \'{member.type}\')')

            a.type = STRUCT(a.name)
        elif isinstance(a,StructAccess):
            type_check_util(a.get_struct())

            st_name = a.get_struct().type.name
            if st_name in st.keys() and a.member in st[st_name].keys():
                a.type = st[st_name][a.member]
            else:
                status = False
                logger.error(f'{a.ln}: Member \'{a.member}\' invalid for struct \'{a.get_struct().name}\'')
        else:
            logger.error(f'{a.ln}: Invalid expression\n\t{a}')
            status = False

    def check_formula_type_util(ast: AST) -> None:
        nonlocal status
        nonlocal formula_type

        if isinstance(ast, FutureTimeOperator):
            if formula_type == FormulaType.PT:
                logger.error(f" Mixed-time MLTL formulas not allowed\n\t{ast}")
                status = False
            else:
                formula_type = FormulaType.FT
        elif isinstance(ast, PastTimeOperator):
            if formula_type == FormulaType.FT:
                logger.error(f" Mixed-time MLTL formulas not allowed\n\t{ast}")
                status = False
            else:
                formula_type = FormulaType.PT

    def set_formula_type_util(ast: AST) -> None:
        nonlocal formula_type
        ast.formula_type = formula_type

    type_check_util(program)

    # check mixed-time formulas, set each node to respective formula type
    for spec in program.specs: 
        formula_type = FormulaType.PROP
        preorder(spec, check_formula_type_util)

        # Set propositional formulas to FT by default
        formula_type = FormulaType.FT if formula_type == FormulaType.PROP else formula_type

        preorder(spec, set_formula_type_util)

    if status:
        program.is_type_correct = True

    return status


def compute_scq_size(a: AST) -> int:
    """
    Computes SCQ sizes for each node in 'a' and returns the sum of each SCQ size. Sets this sum to the total_scq_size value of program.
    """
    visited: list[int] = []
    total: int = 0

    def compute_scq_size_util(a: AST) -> None:
        nonlocal visited
        nonlocal total

        if not isinstance(a, TLInstruction) or isinstance(a, Program) or a.formula_type != FormulaType.FT:
            return

        if isinstance(a, Specification):
            a.scq_size = 1
            total += a.scq_size
            return

        # if len(a.get_children()) > 1:
        #     for child in a.get_children():
        #         max_sibling_wpd: int = max([sib.wpd for sib in a.get_children() if id(sib) != id(child)])
        #         child.scq_size = max(max_sibling_wpd - child.bpd, child.scq_size)

        max_wpd: int = 0
        for p in a.get_parents():
            for s in p.get_children():
                if not id(s) == id(a):
                    max_wpd = s.wpd if s.wpd > max_wpd else max_wpd

        a.scq_size = max(max_wpd-a.bpd,0)+1 # works for +3 b/c of some bug -- ask Brian
        total += a.scq_size

        # print(f"{a}: {a.scq_size}")
 
    postorder(a ,compute_scq_size_util)
    a.total_scq_size = total

    return total


def rewrite_at_filters(program: Program) -> None:

    def rewrite_at_filters_util(a: AST):
        if isinstance(a, RelationalOperator):
            lhs = a.get_lhs()
            rhs: Literal = cast(Literal, a.get_rhs())
            filter_args = cast(list[Literal], lhs.get_children())

            if isinstance(lhs, Function):
                a.replace(ATInstruction(a.ln, lhs.name, deepcopy(a), rhs, filter_args))
            elif isinstance(lhs, Signal):
                a.replace(ATInstruction(a.ln, lhs.type.name, deepcopy(a), rhs, [lhs]))
            else:
                logger.error(f"{a.ln}: Internal error, AT type checker failed.")


    postorder(program, rewrite_at_filters_util)


def rewrite_extended_operators(program: Program) -> None:
    """
    Rewrites program formulas without extended operators i.e., formulas with only negation, conjunction, until, global, and future.

    Preconditions:
        - program is type correct.

    Postconditions:
        - program formulas only have negation, conjunction, until, and global TL operators.
    """
    
    if not program.is_type_correct:
        logger.error(f' Program must be type checked before rewriting.')
        return

    def rewrite_extended_operators_util(a: AST) -> None:

        if isinstance(a, LogicalOperator):
            if isinstance(a, LogicalOr):
                # p || q = !(!p && !q)
                a.replace(LogicalNegate(a.ln, LogicalAnd(a.ln, [LogicalNegate(c.ln, c) for c in a.get_children()])))
            elif isinstance(a, LogicalXor):
                lhs: AST = a.get_lhs()
                rhs: AST = a.get_rhs()
                # p xor q = (p && !q) || (!p && q) = !(!(p && !q) && !(!p && q))
                a.replace(LogicalNegate(a.ln, LogicalAnd(a.ln, [LogicalNegate(a.ln, \
                    LogicalAnd(a.ln, [lhs, LogicalNegate(rhs.ln, rhs)])), LogicalNegate(a.ln, \
                        LogicalAnd(a.ln, [LogicalNegate(lhs.ln, lhs), rhs]))])))
            elif isinstance(a, LogicalImplies):
                lhs: AST = a.get_lhs()
                rhs: AST = a.get_rhs()
                # p -> q = !(p && !q)
                a.replace(LogicalNegate(a.ln, LogicalAnd(lhs.ln, [lhs, LogicalNegate(rhs.ln, rhs)])))
        elif isinstance(a, Release):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()
            bounds: Interval = a.interval
            # p R q = !(!p U !q)
            a.replace(LogicalNegate(a.ln, Until(a.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))
        elif isinstance(a, Future):
            operand: AST = a.get_operand()
            bounds: Interval = a.interval
            # F p = True U p
            a.replace(Until(a.ln, Bool(a.ln, True), operand, bounds.lb, bounds.ub))

    postorder(program, rewrite_extended_operators_util)


def rewrite_boolean_normal_form(program: Program) -> None:
    """
    Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators.
    
    Preconditions:
        - program is type checked

    Postconditions:
        - program formulas are in boolean normal form
    """
    
    if not program.is_type_correct:
        logger.error(f' Program must be type checked before converting to boolean normal form.')
        return

    # TODO check if not in nnf
    
    def rewrite_boolean_normal_form_util(a: AST) -> None:

        if isinstance(a, LogicalOr):
            # p || q = !(!p && !q)
            a.replace(LogicalNegate(a.ln, LogicalAnd(a.ln, [LogicalNegate(c.ln, c) for c in a.get_children()])))
        elif isinstance(a, LogicalImplies):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()
            # p -> q = !(p && !q)
            a.replace(LogicalNegate(a.ln, LogicalAnd(a.ln, [lhs, LogicalNegate(rhs.ln, rhs)])))
        elif isinstance(a, LogicalXor):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()
            # p xor q = !(!p && !q) && !(p && q)
            a.replace(LogicalAnd(a.ln, [LogicalNegate(a.ln, LogicalAnd(lhs.ln, [LogicalNegate(lhs.ln, lhs), \
                LogicalNegate(rhs.ln, rhs)])), LogicalNegate(lhs.ln, LogicalAnd(lhs.ln, [lhs, rhs]))]))
        elif isinstance(a, Future):
            operand: AST = a.get_operand()
            bounds: Interval = a.interval
            # F p = True U p
            a.replace(Until(a.ln, Bool(operand.ln, True), operand, bounds.lb, bounds.ub))
        elif isinstance(a, Global):
            operand: AST = a.get_operand()
            bounds: Interval = a.interval
            # G p = !(True U !p)
            a.replace(LogicalNegate(a.ln, Until(a.ln, Bool(operand.ln, True), LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub)))
        elif isinstance(a, Release):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()
            bounds: Interval = a.interval
            # p R q = !(!p U !q)
            a.replace(LogicalNegate(a.ln, Until(a.ln, LogicalNegate(lhs.ln, lhs), \
                                                      LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))

        for child in a.get_children():
            rewrite_boolean_normal_form_util(child)

    rewrite_boolean_normal_form_util(program)
    program.is_boolean_normal_form = True


def rewrite_negative_normal_form(program: Program) -> None:
    """
    Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals.
    
    Preconditions:
        - program is type checked

    Postconditions:
        - program formulas are in negative normal form
    """
    
    if not program.is_type_correct:
        logger.error(f' Program must be type checked before converting to negative normal form.')
        return

    # TODO check if not in bnf

    def rewrite_negative_normal_form_util(a: AST) -> None:

        if isinstance(a, LogicalNegate):
            operand = a.get_operand()
            if isinstance(operand, LogicalNegate):
                # !!p = p
                a.replace(operand.get_operand())
            if isinstance(operand, LogicalOr):
                # !(p || q) = !p && !q
                a.replace(LogicalAnd(a.ln, [LogicalNegate(c.ln, c) for c in operand.get_children()]))
            if isinstance(operand, LogicalAnd):
                # !(p && q) = !p || !q
                a.replace(LogicalOr(a.ln, [LogicalNegate(c.ln, c) for c in operand.get_children()]))
            elif isinstance(operand, Future):
                bounds: Interval = operand.interval
                # !F p = G !p
                a.replace(Global(a.ln, LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, Global):
                bounds: Interval = operand.interval
                # !G p = F !p
                a.replace(Future(a.ln, LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, Until):
                lhs: AST = operand.get_lhs()
                rhs: AST = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p U q) = !p R !q 
                a.replace(Release(a.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
            elif isinstance(operand, Release):
                lhs: AST = operand.get_lhs()
                rhs: AST = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p R q) = !p U !q
                a.replace(Until(a.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
        elif isinstance(a, LogicalImplies):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()
            # p -> q = !p || q
            a.replace(LogicalOr(a.ln, [LogicalNegate(lhs.ln, lhs), rhs]))
        elif isinstance(a, LogicalXor):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()
            # p xor q = (p && !q) || (!p && q)
            a.replace(LogicalOr(a.ln, [LogicalAnd(a.ln, [lhs, LogicalNegate(rhs.ln, rhs)]),\
                                       LogicalAnd(a.ln, [LogicalNegate(lhs.ln, lhs), rhs])]))

        for child in a.get_children():
            rewrite_negative_normal_form_util(child)

    rewrite_negative_normal_form_util(program)
    program.is_negative_normal_form = True


def rewrite_set_aggregation(program: Program) -> None:
    """
    Rewrites set aggregation operators into corresponding BZ and TL operations e.g., foreach is rewritten into a conjunction.

    Preconditions:
        - program is type correct

    Postconditions:
        - program has no struct access operations
        - program has no variables
    """

    # could be done far more efficiently...currently traverses each set agg
    # expression sub tree searching for struct accesses. better approach: keep
    # track of these accesses on the frontend
    def rewrite_struct_access_util(a: AST) -> None:
        for c in a.get_children():
            rewrite_struct_access_util(c)

        if isinstance(a,StructAccess) and not isinstance(a.get_struct(),Variable):
            s: Struct = a.get_struct()
            a.replace(s.members[a.member])
    
    def rewrite_set_aggregation_util(a: AST) -> None:
        cur: AST = a

        if isinstance(a, ForEach):
            cur = LogicalAnd(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()])
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForSome):
            cur = LogicalOr(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()])
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForExactlyN):
            s: Set = a.get_set()
            cur = Equal(a.ln, Count(a.ln, Integer(a.ln, s.get_max_size()), [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.num)
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForAtLeastN):
            s: Set = a.get_set()
            cur = GreaterThanOrEqual(a.ln, Count(a.ln, Integer(a.ln, s.get_max_size()), [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.num)
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForAtMostN):
            s: Set = a.get_set()
            cur = LessThanOrEqual(a.ln, Count(a.ln, Integer(a.ln, s.get_max_size()), [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.num)
            a.replace(cur)
            rewrite_struct_access_util(cur)

        for c in cur.get_children():
            rewrite_set_aggregation_util(c)

    rewrite_set_aggregation_util(program)
    program.is_set_agg_free = True


def rewrite_struct_access(program: Program) -> None:
    """
    Rewrites struct access operations to the references member expression.

    Preconditions:
        - program is type correct
        - program has no set aggregation operators

    Postconditions:
        - program has no struct access operations
    """
    
    if not program.is_type_correct:
        logger.error(f' Program must be type checked before rewriting struct accesses.')
        return
    if not program.is_set_agg_free:
        logger.error(f' Program must be free of set aggregation operators before rewriting struct accesses.')
        return

    def rewrite_struct_access_util(a: AST) -> None:
        if isinstance(a, StructAccess):
            s: Struct = a.get_struct()
            a.replace(s.members[a.member])

    postorder(program, rewrite_struct_access_util)
    program.is_struct_access_free = True


def optimize_rewrite_rules(program: AST) -> None:

    def optimize_rewrite_rules_util(a: AST) -> None:
        if isinstance(a, LogicalNegate):
            opnd1 = a.get_operand()
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # !true = false
                    a.replace(Bool(a.ln, False))
                else:
                    # !false = true
                    a.replace(Bool(a.ln, True))
            elif isinstance(opnd1, LogicalNegate):
                # !!p = p
                a.replace(opnd1.get_operand())
            elif isinstance(opnd1, Global):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    a.replace(Future(a.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
            elif isinstance(opnd1, Future):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    a.replace(Global(a.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
        elif isinstance(a, Equal):
            lhs = a.get_lhs()
            rhs = a.get_rhs()
            if isinstance(lhs, Bool) and isinstance(rhs, Bool):
                pass
            elif isinstance(lhs, Bool):
                # (true == p) = p
                a.replace(rhs)
            elif isinstance(rhs, Bool):
                # (p == true) = p
                a.replace(lhs)
        elif isinstance(a, Global):
            opnd1 = a.get_operand()
            if a.interval.lb == 0 and a.interval.ub == 0:
                # G[0,0]p = p
                a.replace(opnd1)
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # G[l,u]True = True
                    a.replace(Bool(a.ln, True))
                else:
                    # G[l,u]False = False
                    a.replace(Bool(a.ln, False))
            elif isinstance(opnd1, Global):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = a.interval.lb + opnd1.interval.lb
                ub: int = a.interval.ub + opnd1.interval.ub
                a.replace(Global(a.ln, opnd2, lb, ub))
            elif isinstance(opnd1, Future):
                opnd2 = opnd1.get_operand()
                if a.interval.lb == a.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = a.interval.lb + opnd1.interval.lb
                    ub: int = a.interval.ub + opnd1.interval.ub
                    a.replace(Future(a.ln, opnd2, lb, ub))
        elif isinstance(a, Future):
            opnd1 = a.get_operand()
            if a.interval.lb == 0 and a.interval.ub == 0:
                # F[0,0]p = p
                a.replace(opnd1)
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # F[l,u]True = True
                    a.replace(Bool(a.ln, True))
                else:
                    # F[l,u]False = False
                    a.replace(Bool(a.ln, False))
            elif isinstance(opnd1, Future):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = a.interval.lb + opnd1.interval.lb
                ub: int = a.interval.ub + opnd1.interval.ub
                a.replace(Future(a.ln, opnd2, lb, ub))
            elif isinstance(opnd1, Global):
                opnd2 = opnd1.get_operand()
                if a.interval.lb == a.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = a.interval.lb + opnd1.interval.lb
                    ub: int = a.interval.ub + opnd1.interval.ub
                    a.replace(Global(a.ln, opnd2, lb, ub))
        elif isinstance(a, LogicalAnd):
            # Assume binary for now
            lhs = a.get_child(0)
            rhs = a.get_child(1)
            if isinstance(lhs, Global) and isinstance(rhs, Global):
                p = lhs.get_operand()
                q = rhs.get_operand()
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q): # check syntactic equivalence
                    # G[lb1,lb2]p && G[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        a.replace(Global(a.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        a.replace(Global(a.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        a.replace(Global(a.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        a.replace(Global(a.ln, p, lb2, max(ub1,ub2)))
                        return

                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                a.replace(Global(a.ln, LogicalAnd(a.ln, 
                        [Global(a.ln, p, lb1-lb3, ub1-ub3), Global(a.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
            elif isinstance(lhs, Future) and isinstance(rhs, Future):
                lhs_opnd = lhs.get_operand()
                rhs_opnd = rhs.get_operand()
                if str(lhs_opnd) == str(rhs_opnd): # check for syntactic equivalence
                    # F[l1,u1]p && F[l2,u2]p = F[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and lb1 <= ub2:
                        # l2 <= l1 <= u2
                        a.replace(Future(a.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        a.replace(Future(a.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    a.replace(Until(a.ln, LogicalAnd(a.ln, [lhs_lhs, rhs_lhs]), lhs_rhs, lhs.interval.lb, 
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(a, LogicalOr):
            # Assume binary for now
            lhs = a.get_child(0)
            rhs = a.get_child(1)
            if isinstance(lhs, Future) and isinstance(rhs, Future):
                p = lhs.get_operand()
                q = rhs.get_operand()
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q):
                    # F[lb1,lb2]p || F[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        a.replace(Future(a.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        a.replace(Future(a.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        a.replace(Future(a.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        a.replace(Future(a.ln, p, lb2, max(ub1,ub2)))
                        return

                # TODO: check for when lb==ub==0
                # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                a.replace(Future(a.ln, LogicalOr(a.ln, 
                        [Future(a.ln, p, lb1-lb3, ub1-ub3), Future(a.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
            elif isinstance(lhs, Global) and isinstance(rhs, Global):
                lhs_opnd = lhs.get_operand()
                rhs_opnd = rhs.get_operand()
                if str(lhs_opnd) == str(rhs_opnd):
                    # G[l1,u1]p || G[l2,u2]p = G[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and lb1 <= ub2:
                        # l2 <= l1 <= u2
                        a.replace(Global(a.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        a.replace(Global(a.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    a.replace(Until(a.ln, LogicalOr(a.ln, [lhs_rhs, rhs_rhs]), lhs_lhs, lhs.interval.lb, 
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(a, Until):
            lhs = a.get_lhs()
            rhs = a.get_rhs()
            if isinstance(rhs, Global) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                a.replace(Global(a.ln, lhs, a.interval.lb, a.interval.lb+rhs.interval.ub))
            elif isinstance(rhs, Future) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                a.replace(Future(a.ln, lhs, a.interval.lb, a.interval.lb+rhs.interval.ub))

    postorder(program, optimize_rewrite_rules_util)


def optimize_stratify_associative_operators(a: AST) -> None:
    
    def optimize_associative_operators_rec(a: AST) -> None:
        if isinstance(a, LogicalAnd) and len(a.get_children()) > 2:
            n: int = len(a.get_children())
            children = [c for c in a.get_children()]
            wpds = [c.wpd for c in children]
            wpds.sort(reverse=True)

            T = max(children, key=lambda c: c.wpd)
            # print('max:')
            # print(T)

            if (n-2)*(wpds[0]-wpds[1])-wpds[2]+min([c.bpd for c in a.get_children() if c.wpd < wpds[0]]):
                a.replace(LogicalAnd(a.ln, [LogicalAnd(a.ln, [c for c in children if c != children[0]]), children[0]]))
                children[0].get_parents().remove(a)

        elif isinstance(a, LogicalOr):
            max_wpd: int = max([c.wpd for c in a.get_children()])
            target: AST = next(c for c in a.get_children() if c.wpd == max_wpd)

            new_children = [c for c in a.get_children() if c != target]
            new_ast = LogicalOr(a.ln, [LogicalOr(a.ln, new_children), target])

            if compute_scq_size(new_ast) < compute_scq_size(a):
                # (a0 && a1 && ... && an) = ((a1 && a2 && ... && an-1) && an)
                a.replace(new_ast)

        for c in a.get_children():
            optimize_associative_operators_rec(c)

    optimize_associative_operators_rec(a)


def optimize_cse(program: Program) -> None:
    """
    Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence.

    Preconditions:
        - program is type correct

    Postconditions:
        - program has no distinct, syntactically equivalent sub-expressions (i.e., is CSE reduced)
    """
    
    if not program.is_type_correct:
        logger.error(f' Program must be type checked before CSE.')
        return

    S: dict[str,AST] = {}
    
    def optimize_cse_util(a: AST) -> None:
        nonlocal S
        c: int
        i: str

        for c in range(0,a.num_children()):
            i = str(a.get_child(c))

            if i in S.keys():
                a.get_child(c).replace(S[i])
            else:
                S[i] = a.get_child(c)
    
    postorder(program, optimize_cse_util)
    program.is_cse_reduced = True


# def generate_alias(program: Program) -> str:
#     """
#     Generates string corresponding to the alias file for th argument program. The alias file is used by R2U2 to print formula labels and contract status.

#     Preconditions:
#         - program is type correct

#     Postconditions:
#         - None
#     """
#     s: str = ''

#     for spec in program.specs:
#         if isinstance(spec, Contract):
#             continue
#         s += 'F ' + spec.name + ' ' + str(spec.formula_number) + '\n'

#     for contract in program.contracts:
#         s += 'C ' + contract.name + ' ' + str(contract.formula_number) + ' ' + \
#             str(contract.formula_number+1) + ' ' + str(contract.formula_number+2) + '\n'

#     return s


def parse_signals(filename: str) -> dict[str,int]:
    mapping: dict[str,int] = {}
    if re.match('.*\\.csv',filename):
        with open(filename,'r') as f:
            text: str = f.read()
            lines: list[str] = text.splitlines()
            if len(lines) < 1:
                logger.error(f' Not enough data in file \'{filename}\'')
                return {}
            cnt: int = 0
            header = lines[0][1:] if lines[0][0] == '#' else lines[0]
            for id in [s.strip() for s in header.split(',')]:
                mapping[id] = cnt
                cnt += 1
    else: # TODO, implement signal mapping file format
        return {}

    return mapping
    

def rewrite_implicit_signal_loads(program: Program) -> None:

    def rewrite_implicit_signal_loads_util(ast: AST) -> None:
        if isinstance(ast, TLInstruction):
            for child in ast.get_children():
                if isinstance(child, Signal):
                    one = Integer(child.ln, 1)
                    child_copy = deepcopy(child)
                    child.replace(ATInstruction(child.ln, "int", Equal(child.ln, child_copy, one), one, [child_copy]))

    postorder(program, rewrite_implicit_signal_loads_util)


def insert_stores_loads(program: Program, at: bool, bz: bool) -> None:

    def insert_stores_loads_util(ast: AST) -> None:
        # print(f"{type(ast)} : {id(ast)} : {ast}")
        if isinstance(ast, TLInstruction):
            for child in ast.get_children():
                if isinstance(child, BZInstruction):
                    child.replace(TLAtomicLoad(child.ln, BZAtomicStore(child.ln, child)))
                elif isinstance(child, ATInstruction):
                    child.replace(TLAtomicLoad(child.ln, deepcopy(child)))

    postorder(program, insert_stores_loads_util)


def assign_ids(program: Program, at: bool, bz: bool, signal_mapping: dict[str,int]) -> None:
    tlid: int = 0
    atid: int = 0

    def assign_ids_util(a: AST) -> None:
        nonlocal signal_mapping
        nonlocal tlid
        nonlocal atid

        if isinstance(a, Bool) or a.tlid > -1 or a.atid > -1:
            return

        if isinstance(a, TLInstruction):
            a.tlid = tlid
            tlid += 1
        elif bz and isinstance(a, BZAtomicStore):
            a.atid = atid
            atid += 1
        elif at and isinstance(a, ATInstruction):
            a.atid = atid
            atid += 1
        elif isinstance(a, Signal):
            if not a.name in signal_mapping.keys():
                logger.error(f'{a.ln}: Signal \'{a}\' not referenced in signal mapping')
            else:
                a.sid = signal_mapping[a.name]
                    
    postorder(program,assign_ids_util)


def generate_assembly(program: Program, at: bool, bz: bool, signal_mapping: dict[str,int]) -> list[Instruction]:
    visited: set[AST] = set()
    asm: list[Instruction] = []
    status: bool = True

    def generate_assembly_util(a: AST) -> None:
        nonlocal visited
        nonlocal asm
        nonlocal status

        if isinstance(a, TLInstruction):
            # each TL instruction is generated exactly once
            if not a in visited:
                # postorder traversal
                for child in a.get_children():
                    generate_assembly_util(child)
                asm.append(a)
                visited.add(a)
        elif at and isinstance(a, ATInstruction):
            # each AT instruction is generated exactly once
            if not a in visited:
                # postorder traversal, only other AT instructions
                for child in [c for c in a.get_children() if isinstance(c, ATInstruction)]:
                    generate_assembly_util(child)
                asm.append(a)
                visited.add(a)
        elif bz and isinstance(a, BZInstruction):
            # each BZ instruction is generated as many times as needed
            for child in a.get_children():
                generate_assembly_util(child)
            asm.append(a)
        elif not isinstance(a, Bool):
            logger.error(f'{a.ln}: Internal error, invalid node type for assembly generation ({type(a)})')

    insert_stores_loads(program, at, bz)
    assign_ids(program, at, bz, signal_mapping)
    
    # postorder(program, generate_assembly_util)
    generate_assembly_util(program)
    program.assembly = asm
    
    return asm if status else []


def generate_scq_assembly(program: Program) -> list[tuple[int,int]]:
    ret: list[tuple[int,int]] = []
    pos: int = 0
    visited: set[AST] = set()

    compute_scq_size(program)

    def gen_scq_assembly_util(a: AST) -> None:
        nonlocal ret
        nonlocal pos
        nonlocal visited

        if a in visited:
            return

        if not isinstance(a, TLInstruction) or isinstance(a, Program) or a.formula_type != FormulaType.FT:
            return

        # print(f"{type(a)}")

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        ret.append((start_pos,end_pos))

        # print(f"{a} : ({start_pos}, {end_pos})")

        visited.add(a)

    postorder(program, gen_scq_assembly_util)
    program.scq_assembly = ret

    return ret


def compute_cpu_wcet(program: Program, latency_table: dict[str, int], clk: int) -> int:
    """
    Compute and return worst-case execution time in clock cycles for software version R2U2 running on a CPU. Sets this total to the cpu_wcet value of program.

    latency_table is a dictionary that maps the class names of AST nodes to their estimated computation time in CPU clock cycles. For instance, one key-value pair may be ('LogicalAnd': 15). If an AST node is found that does not have a corresponding value in the table, an error is reported.

    Preconditions:
        - program has had its assembly generated

    Postconditions:
        - None
    """
    wcet: int = 0

    def compute_cpu_wcet_util(a: AST) -> int:
        nonlocal latency_table

        classname: str = type(a).__name__
        if classname not in latency_table:
            logger.error(f' Operator \'{classname}\' not found in CPU latency table.')
            return 0
        else:
            return int((latency_table[classname] * a.scq_size) / clk)

    wcet = sum([compute_cpu_wcet_util(a) for a in program.assembly])
    program.cpu_wcet = wcet
    return wcet


def compute_fpga_wcet(program: Program, latency_table: dict[str, tuple[float, float]], clk: float) -> float:
    """
    Compute and return worst-case execution time in micro seconds for hardware version R2U2 running on an FPGA. Sets this total to the fpga_wcet value of program.

    latency_table is a dictionary that maps the class names of AST nodes to their estimated computation time in micro seconds. For instance, one key-value pair may be ('LogicalAnd': 15.0). If an AST node is found that does not have a corresponding value in the table, an error is reported.

    Preconditions:
        - program has had its assembly generated

    Postconditions:
        - None
    """
    wcet: float = 0

    def compute_fpga_wcet_util(a: AST) -> float:
        nonlocal latency_table

        classname: str = type(a).__name__
        if classname not in latency_table:
            logger.error(f' Operator \'{classname}\' not found in FPGA latency table.')
            return 0
        else:
            sum_scq_sizes_children = sum([c.scq_size for c in a.get_children()])
            return latency_table[classname][0] + latency_table[classname][1]*sum_scq_sizes_children

    wcet = sum([compute_fpga_wcet_util(a) for a in program.assembly]) / clk
    program.fpga_wcet = wcet
    return wcet


def validate_booleanizer_stack(asm: list[Instruction]) -> bool:
    """
    Performs basic validation of the Booleanizer instructions of the generated assembly. Returns False if the stack size ever goes below 0 or above its maximum size.
    """
    max_stack_size: int = 32
    stack_size: int = 0

    def is_invalid_stack_size(size: int) -> bool:
        return size < 0 and size >= max_stack_size

    for instruction in [a for a in asm if isinstance(a, BZInstruction)]:
        if is_invalid_stack_size(stack_size):
            return False

        # Pop all instruction operands 
        stack_size -= len(instruction.get_children())

        if is_invalid_stack_size(stack_size):
            return False

        # Push result
        stack_size += 1

        if is_invalid_stack_size(stack_size):
            return False

    return True


def parse(input: str) -> list[Program]:
    lexer: C2POLexer = C2POLexer()
    parser: C2POParser = C2POParser()
    return parser.parse(lexer.tokenize(input))


def compile(
    input_filename: str, 
    signals_filename: str, 
    output_path: str = 'config/', 
    impl: str = 'c', 
    int_width: int = 8, 
    int_signed: bool = False, 
    float_width: int = 32, 
    cse: bool = True, 
    at: bool = False, 
    bz: bool = False, 
    extops: bool = True, 
    color: bool = True, 
    quiet: bool = False
) -> int:
    """Compiles a C2PO input file and outputs generated R2U2 assembly/binaries"""
    INT.width = int_width
    INT.is_signed = int_signed
    FLOAT.width = float_width

    if bz and at:
        logger.error(f" Only one of AT and BZ can be enabled")
        return ReturnCode.ENGINE_SELECT_ERROR.value

    # parse input, programs is a list of configurations (each SPEC block is a configuration)
    with open(input_filename, "r") as f:
        programs: list[Program] = parse(f.read())

    if len(programs) < 1:
        logger.error(' Failed parsing.')
        return ReturnCode.PARSE_ERROR.value

    for program in programs:
        # type check
        if not type_check(program, at, bz, program.structs):
            logger.error(' Failed type check.')
            return ReturnCode.TYPE_CHECK_ERROR.value

        # Separate FT/PT formulas
        ft_specs = [spec for spec in program.specs if spec.formula_type == FormulaType.FT]

        ft_contracts = {}
        for label,(f1,f2,f3) in program.contracts.items():
            for spec in ft_specs:
                if spec.name == label:
                    ft_contracts[label] = (f1,f2,f3)

        ft_program = Program(
            program.ln, 
            program.structs, 
            ft_contracts,
            ft_specs
        )
        ft_program.is_type_correct = True

        pt_specs = [spec for spec in program.specs if spec.formula_type == FormulaType.PT]

        pt_contracts = {}
        for label,(f1,f2,f3) in program.contracts.items():
            for spec in pt_specs:
                if spec.name == label:
                    pt_contracts[label] = (f1,f2,f3)

        pt_program = Program(
            program.ln, 
            program.structs, 
            pt_contracts,
            pt_specs
        )
        pt_program.is_type_correct = True

        for prog in [ft_program, pt_program]:
            rewrite_set_aggregation(prog)
            rewrite_struct_access(prog)
            rewrite_at_filters(prog)
            if at:
                rewrite_implicit_signal_loads(program)

            # rewrite without extended operators if enabled
            if not extops:
                rewrite_extended_operators(prog)

            optimize_rewrite_rules(prog)

            # common sub-expressions elimination
            if cse:
                optimize_cse(prog)

            # generate alias file
            # alias = gen_alias(prog)

            # parse csv/signals file
            signal_mapping: dict[str,int] = parse_signals(signals_filename)

            # generate assembly
            asm: list[Instruction] = generate_assembly(prog, at, bz, signal_mapping)
            scq_asm: list[tuple[int,int]] = generate_scq_assembly(prog)

            if bz and not validate_booleanizer_stack(asm):
                logger.error(f' Internal error: Booleanizer stack size potentially invalid during execution.')
                return ReturnCode.ASM_ERROR.value

            # print asm if 'quiet' option not enabled
            if not quiet:
                print(f"{Color.HEADER}Generated Assembly{Color.ENDC}:")
                for a in asm:
                    print(f"\t{a.asm()}")
                print(f"{Color.HEADER}Generated SCQs{Color.ENDC}:")
                for s in scq_asm:
                    print(f"\t{s}")

    return ReturnCode.SUCCESS.value

