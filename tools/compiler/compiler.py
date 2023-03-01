from argparse import PARSER
import re
from logging import getLogger

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


def type_check(program: Program, bz: bool, st: StructDict) -> bool:
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

    def type_check_util(a: AST) -> None:
        nonlocal status

        if a in explored:
            return
        explored.append(a)

        if not bz and isinstance(a,BZInstruction) and not isinstance(a,Signal) and not isinstance(a,Bool):
            status = False
            logger.error('%d: Found BZ expression, but Booleanizer expressions disabled\n\t%s', a.ln, a)

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

            a.type = BOOL()
        elif isinstance(a, ArithmeticOperator):
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

            # check for mixed-time formulas
            if isinstance(a, FutureTimeOperator):
                for c in a.get_children():
                    if c.formula_type == FormulaType.PT:
                        status = False
                        logger.error(f'{a.ln}: Mixed-time formulas unsupported\n\t{a}')
                a.formula_type = FormulaType.FT
            elif isinstance(a, PastTimeOperator):
                for c in a.get_children():
                    if c.formula_type == FormulaType.FT:
                        status = False
                        logger.error(f'{a.ln}: Mixed-time formulas unsupported\n\t{a}')
                a.formula_type = FormulaType.PT
            else:
                # not a TL op, propagate formula type from children
                for c in a.get_children():
                    if c.formula_type == FormulaType.FT or c.formula_type == FormulaType.PT:
                        a.formula_type = c.formula_type

            if a.interval.lb > a.interval.ub:
                status = status
                logger.error(f'{a.ln}: Future time interval invalid, lower bound must less than or equal to upper bound (found [{a.interval.lb},{a.interval.ub}])')

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

    type_check_util(program)

    if status:
        program.is_type_correct = True

    return status


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


def optimize_rewrite_rules(program: Program) -> None:
    rules = { '' : '' }

    def optimize_rewrite_rules_util(a: AST) -> None:
        if isinstance(a, LogicalNegate):
            opnd1 = a.get_operand()
            if isinstance(opnd1, Global):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    a.replace(Future(a.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
            if isinstance(opnd1, Future):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    a.replace(Global(a.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
        elif isinstance(a, Global):
            opnd1 = a.get_operand()
            if a.interval.lb == 0 and a.interval.ub == 0:
                # G[0,0]p = p
                a.replace(opnd1)
            if isinstance(opnd1, Bool):
                if opnd1.val == True:
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
                a.replace(Global(a.ln, opnd1, lb, ub))
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
                if opnd1.val == True:
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
                a.replace(Future(a.ln, opnd1, lb, ub))
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

                if p == q:
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

                # TODO: check for when lb==ub==0
                # (G[l1,u1]p) && (G[l2,u2]q) = G[l3,u3](G[l1-l3,u1-u3]p && G[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)
                a.replace(Global(a.ln, LogicalAnd(a.ln, 
                    [Global(a.ln, p, lb1-lb3, ub1-ub3), Global(a.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
            elif isinstance(lhs, Future) and isinstance(rhs, Future):
                lhs_opnd = lhs.get_operand()
                rhs_opnd = rhs.get_operand()
                if lhs_opnd == rhs_opnd:
                    # F[l1,u1]p && F[l2,u2]p = F[max(l1,l2),min(u1,u2)]p
                    pass
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if lhs_rhs == rhs_rhs and lhs.interval.lb == rhs.interval.lb:
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

                if p == q:
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
                if lhs_opnd == rhs_opnd:
                    # G[l1,u1]p || G[l2,u2]p = G[max(l1,l2),min(u1,u2)]p
                    pass
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if lhs_lhs == rhs_lhs and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    a.replace(Until(a.ln, LogicalOr(a.ln, [lhs_rhs, rhs_rhs]), lhs_lhs, lhs.interval.lb, 
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(a, Until):
            lhs = a.get_lhs()
            rhs = a.get_rhs()
            if isinstance(rhs, Global) and rhs.interval.lb == 0 and lhs == rhs.get_operand():
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                a.replace(Global(a.ln, lhs, a.interval.lb, a.interval.lb+rhs.interval.ub))
            if isinstance(rhs, Future) and rhs.interval.lb == 0 and lhs == rhs.get_operand():
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                a.replace(Future(a.ln, lhs, a.interval.lb, a.interval.lb+rhs.interval.ub))

        

    postorder(program, optimize_rewrite_rules_util)


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


def generate_alias(program: Program) -> str:
    """
    Generates string corresponding to the alias file for th argument program. The alias file is used by R2U2 to print formula labels and contract status.

    Preconditions:
        - program is type correct

    Postconditions:
        - None
    """
    s: str = ''

    for spec in program.specs:
        if spec.name in [c.name for c in program.contracts.values()]: 
            # then formula is part of contract, ignore
            continue
        s += 'F ' + spec.name + ' ' + str(spec.formula_number) + '\n'

    for num,contract in program.contracts.items():
        s += 'C ' + contract.name + ' ' + str(num) + ' ' + \
            str(num+1) + ' ' + str(num+2) + '\n'

    return s


def compute_scq_size(program: Program) -> int:
    """
    Computes SCQ sizes for each node in 'program' and returns the sum of each SCQ size. Sets this sum to the total_scq_size value of program.
    """
    visited: list[AST] = []
    total: int = 0

    def compute_scq_size_util(a: AST) -> None:
        nonlocal visited
        nonlocal total

        if not isinstance(a, TLInstruction) or isinstance(a, Program):
            return

        if a in visited:
            return
        visited.append(a)

        if isinstance(a, Specification):
            a.scq_size = 1
            total += a.scq_size
            return

        siblings: list[AST] = []
        for p in a.get_parents():
            for s in p.get_children():
                if not s == a:
                    siblings.append(s)

        wpd: int = max([s.wpd for s in siblings]+[0])

        a.scq_size = max(wpd-a.bpd,0)+1 # works for +3 b/c of some bug -- ask Brian
        total += a.scq_size

        print(f"{a}: {a.scq_size}")
 
    postorder(program,compute_scq_size_util)
    program.total_scq_size = total

    return total


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
    

def assign_ids(program: Program, signal_mapping: dict[str,int]) -> None:
    tlid: int = 0
    bzid: int = 0
    atid: int = 0

    def assign_ids_util(a: AST) -> None:
        nonlocal signal_mapping
        nonlocal tlid
        nonlocal bzid
        nonlocal atid

        if isinstance(a,Bool) or a.tlid > -1 or a.bzid > -1:
            return

        if isinstance(a,TLInstruction):
            a.tlid = tlid
            tlid += 1

        if isinstance(a,BZInstruction):
            for p in a.get_parents():
                if isinstance(p,TLInstruction):
                    a.atid = atid
                    atid += 1
                    a.tlid = tlid
                    tlid += 1
                    break

        if isinstance(a,Signal):
            if not a.name in signal_mapping.keys():
                logger.error(f'{a.ln}: Signal \'{a}\' not referenced in signal mapping')
            else:
                a.sid = signal_mapping[a.name]
            
            for p in a.get_parents():
                if isinstance(p,TLInstruction):
                    a.tlid = tlid
                    tlid += 1
                    break
                    
    postorder(program,assign_ids_util)


def generate_assembly(program: Program, signal_mapping: dict[str,int]) -> list[Instruction]:
    visited: set[AST] = set()
    available_registers: set[int] = set()
    max_register: int = 0
    asm: list[Instruction] = []

    # logger.info(program)

    def generate_assembly_util(a: AST) -> None:
        nonlocal visited
        nonlocal available_registers
        nonlocal max_register
        nonlocal asm

        # Visit each TL node exactly once
        # Visit BZ literals as many times as necessary
        # Visit all other BZ nodes once, store and load using registers

        if isinstance(a,TLInstruction):
            for c in a.get_children():
                if isinstance(c, Signal) and not c in visited:
                    asm.append(TLSignalLoad(c.ln, c))
                    visited.add(c)
                elif isinstance(c, Bool) and not c in visited:
                    visited.add(c)
                elif not c in visited:
                    generate_assembly_util(c)

            asm.append(a)
            visited.add(a)
        elif isinstance(a,BZInstruction):
            for c in a.get_children():
                if isinstance(c, Signal):
                    asm.append(BZSignalLoad(c.ln, c))
                else:
                    generate_assembly_util(c)
            
            asm.append(a)

            if not a in visited and a.num_tl_parents > 0:
                asm.append(BZAtomicStore(a.ln, a))
                asm.append(TLAtomicLoad(a.ln, a))

            visited.add(a)
        else:
            logger.error(f'{a.ln}: Invalid node type for assembly generation ({type(a)})')

    assign_ids(program,signal_mapping)
    
    generate_assembly_util(program)
    program.assembly = asm
    
    return asm


def generate_scq_assembly(program: Program) -> list[tuple[int,int]]:
    ret: list[tuple[int,int]] = []
    pos: int = 0

    compute_scq_size(program)

    def gen_scq_assembly_util(a: AST) -> None:
        nonlocal ret
        nonlocal pos

        if isinstance(a,Program) or not isinstance(a,TLInstruction):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        ret.append((start_pos,end_pos))

    postorder(program,gen_scq_assembly_util)
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


def compile(input: str, sigs: str, output_path: str = 'config/', impl: str = 'c', int_width: int = 8, int_signed: bool = False, 
        float_width: int = 32, cse: bool = True, bz: bool = False, extops: bool = True, color: bool = True, quiet: bool = False) -> int:
    INT.width = int_width
    INT.is_signed = int_signed
    FLOAT.width = float_width

    # parse input, programs is a list of configurations (each SPEC block is a configuration)
    programs: list[Program] = parse(input)

    if len(programs) < 1:
        logger.error(' Failed parsing.')
        return ReturnCode.PARSE_ERROR.value

    # type check
    if not type_check(programs[0],bz,programs[0].structs):
        logger.error(' Failed type check.')
        return ReturnCode.TYPE_CHECK_ERROR.value

    pre_memory = compute_scq_size(programs[0])
    print(programs[0])

    rewrite_set_aggregation(programs[0])
    rewrite_struct_access(programs[0])

    # rewrite without extended operators if enabled
    if not extops:
        rewrite_extended_operators(programs[0])

    # common sub-expressions elimination
    if cse:
        optimize_cse(programs[0])

    optimize_rewrite_rules(programs[0])

    post_memory = compute_scq_size(programs[0])

    print(programs[0])
    print(f"{pre_memory},{post_memory}")

    return ReturnCode.SUCCESS.value


    # generate alias file
    # alias = gen_alias(programs[0])

    # parse csv/signals file
    signal_mapping: dict[str,int] = parse_signals(sigs)

    # generate assembly
    asm: list[Instruction] = generate_assembly(programs[0],signal_mapping)
    scq_asm: list[tuple[int,int]] = generate_scq_assembly(programs[0])

    if not validate_booleanizer_stack(asm):
        logger.error(f' Internal error: Booleanizer stack size potentially invalid during execution.')
        return ReturnCode.ASM_ERROR.value

    # print asm if 'quiet' option not enabled
    if not quiet:
        print(Color.HEADER+'Generated Assembly'+Color.ENDC+':')
        for a in asm:
            print('\t'+a.asm())
        print(Color.HEADER+'Generated SCQs'+Color.ENDC+':')
        for s in scq_asm:
            print('\t'+str(s))

    return ReturnCode.SUCCESS.value
