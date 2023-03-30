from argparse import PARSER
import inspect
import sys
import re
from logging import getLogger
# from time import perf_counter

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

# Stores the sub-classes of Instruction from ast.py
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


def type_check(program: Program, at: bool, bz: bool) -> bool:
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
    explored: list[Node] = []
    context: dict[str,Type] = {}
    st: StructDict = program.structs
    formula_type: FormulaType = FormulaType.PROP

    def type_check_util(node: Node) -> None:
        nonlocal formula_type
        nonlocal status

        if node in explored:
            return
        explored.append(node)

        node.formula_type = formula_type

        if isinstance(node, Constant):
            return
        if isinstance(node, Signal):
            if at:
                if node.name in program.signal_mapping:
                    node.sid = program.signal_mapping[node.name]
                    one = Integer(node.ln, 1)
                    a_copy = deepcopy(node)
                    instr = ATInstruction(node.ln, node.name, 'int', [a_copy], Equal(node.ln, a_copy, one), one)
                    program.atomics[node.name] = instr
                    node.replace(Atomic(node.ln, node.name))
                else:
                    status = False
                    logger.error(f'{node.ln}: Non-Boolean signals not allowed in specifications when AT enabled.\n\t{node}')
            else:
                if node.name in program.signal_mapping:
                    node.sid = program.signal_mapping[node.name]
                else:
                    status = False
                    logger.error(f'{node.ln}: Signal \'{node.name}\' not referenced in signal mapping.')

                if not bz: # neither at nor bz are enabled
                    node.replace(Atomic(node.ln, node.name))

        elif isinstance(node, SpecificationSet):
            for c in node.get_children():
                type_check_util(c)
        elif isinstance(node,Specification):
            child = node.get_expr()
            type_check_util(child)

            if not child.type == BOOL():
                status = False
                logger.error(f'{node.ln}: Specification must be of boolean type (found \'{child.type}\')\n\t{node}')
        elif isinstance(node, Contract):
            assume: TLInstruction = node.get_assumption()
            guarantee: TLInstruction = node.get_guarantee()

            type_check_util(assume)
            type_check_util(guarantee)

            if not assume.type == BOOL():
                status = False
                logger.error(f'{node.ln}: Assumption must be of boolean type (found \'{assume.type}\')\n\t{node}')

            if not guarantee.type == BOOL():
                status = False
                logger.error(f'{node.ln}: Guarantee must be of boolean type (found \'{guarantee.type}\')\n\t{node}')
        elif isinstance(node, Atomic):
            if not at:
                status = False
                logger.error(f"{node.ln}: Atomic '{node.name}' referenced, but atomic checker disabled.")
        elif isinstance(node,RelationalOperator):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            type_check_util(lhs)
            type_check_util(rhs)

            if isinstance(node,Equal) or isinstance(node,NotEqual):
                if not is_integer_type(lhs.type) or not is_integer_type(rhs.type):
                    status = False
                    logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', must be of integer type (found \'{lhs.type}\' and \'{rhs.type}\')\n\t{node}')

            if lhs.type != rhs.type:
                status = False
                logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', must be of same type (found \'{lhs.type}\' and \'{rhs.type}\')\n\t{node}')

            if at: # AT checkers restrict the usage of comparison operators
                if not isinstance(lhs, Signal) and not isinstance(lhs, Function):
                    status = False
                    logger.error(f'{node.ln}: Left-hand argument for AT checker must be signal or filter (found {lhs}\n\t{node}')
                if not isinstance(rhs, Literal):
                    status = False
                    logger.error(f'{node.ln}: Right-hand argument for AT checker must be signal or constant (found {rhs}\n\t{node}')

            node.type = BOOL()
        elif isinstance(node, ArithmeticOperator):
            if not bz:
                status = False
                logger.error(f'{node.ln}: Found BZ expression, but Booleanizer expressions disabled\n\t{node}')

            for c in node.get_children():
                type_check_util(c)
            t: Type = node.get_child(0).type

            if isinstance(node, ArithmeticDivide):
                rhs: Node = node.get_rhs()
                if isinstance(rhs, Constant) and rhs.get_value() == 0:
                    status = False
                    logger.error(f'{node.ln}: Divide by zero\n\t{node}')

            for c in node.get_children():
                if c.type != t:
                    status = False
                    logger.error(f'{node.ln}: Operand of \'{node}\' must be of homogeneous type (found \'{c.type}\' and \'{t}\')')

            node.type = t
        elif isinstance(node, BitwiseOperator):
            status = False
            logger.error(f'{node.ln}: Bitwise operators unsupported.\n\t{node}')
        elif isinstance(node, LogicalOperator):
            for c in node.get_children():
                type_check_util(c)
                if c.type != BOOL():
                    status = False
                    logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{node}')

            node.type = BOOL()
        elif isinstance(node, TemporalOperator):
            for c in node.get_children():
                type_check_util(c)
                if c.type != BOOL():
                    status = False
                    logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{node}')

            # check for mixed-time formulas
            if isinstance(node, FutureTimeOperator):
                if formula_type == FormulaType.PT:
                    status = False
                    logger.error(f'{node.ln}: Mixed-time formulas unsupported, found FT formula in PTSPEC.\n\t{node}')
            elif isinstance(node, PastTimeOperator):
                if formula_type == FormulaType.FT:
                    status = False
                    logger.error(f'{node.ln}: Mixed-time formulas unsupported, found PT formula in FTSPEC.\n\t{node}')

            if node.interval.lb > node.interval.ub:
                status = status
                logger.error(f'{node.ln}: Time interval invalid, lower bound must less than or equal to upper bound (found [{node.interval.lb},{node.interval.ub}])')

            node.type = BOOL()
        elif isinstance(node,Set):
            t: Type = NOTYPE()
            for m in node.get_children():
                type_check_util(m)
                t = m.type

            for m in node.get_children():
                if m.type != t:
                    status = False
                    logger.error(f'{node.ln}: Set \'{node}\' must be of homogeneous type (found \'{m.type}\' and \'{t}\')')

            node.type = SET(t)
        elif isinstance(node,Variable):
            if node.name in context.keys():
                node.type = context[node.name]
            else:
                status = False
                logger.error(f'{node.ln}: Variable \'{node}\' not recognized')
        elif isinstance(node,SetAggOperator):
            s: Set = node.get_set()
            boundvar: Variable = node.get_boundvar()

            type_check_util(s)

            if isinstance(s.type, SET):
                context[boundvar.name] = s.type.member_type
            else:
                status = False
                logger.error(f'{node.ln}: Set aggregation set must be Set type (found \'{s.type}\')')

            if isinstance(node, ForExactlyN) or isinstance(node, ForAtLeastN) or isinstance(node, ForAtMostN):
                n: Node = node.num
                type_check_util(n)
                if not is_integer_type(n.type):
                    status = False
                    logger.error(f'{node.ln}: Parameter for set aggregation must be integer type (found \'{n.type}\')')

            expr: Node = node.get_expr()
            type_check_util(expr)

            if expr.type != BOOL():
                status = False
                logger.error(f'{node.ln}: Set aggregation argument must be Boolean (found \'{expr.type}\')')

            del context[boundvar.name]
            explored.remove(boundvar)
            node.type = BOOL()
        elif isinstance(node,Struct):
            for name,member in node.get_members().items():
                type_check_util(member)
                if st[node.name][name] != member.type:
                    logger.error(f'{node.ln}: Member \'{name}\' invalid type for struct \'{node.name}\' (expected \'{st[node.name][name]}\' but got \'{member.type}\')')

            node.type = STRUCT(node.name)
        elif isinstance(node,StructAccess):
            type_check_util(node.get_struct())

            st_name = node.get_struct().type.name
            if st_name in st.keys() and node.member in st[st_name].keys():
                node.type = st[st_name][node.member]
            else:
                status = False
                logger.error(f'{node.ln}: Member \'{node.member}\' invalid for struct \'{node.get_struct().name}\'')
        else:
            logger.error(f'{node.ln}: Invalid expression\n\t{node}')
            status = False

    def type_check_atomic(name: str, node: Node) -> ATInstruction|None:
        nonlocal status

        if isinstance(node, RelationalOperator):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()

            filter: str = ""
            filter_args: list[Node] = []

            # type check left-hand side
            if isinstance(lhs, Function):
                if lhs.name in at_filter_table:
                    if len(at_filter_table[lhs.name][1]) == len(lhs.get_children()):
                        for i in range(0, len(lhs.get_children())):
                            arg: Node = lhs.get_child(i)
                            if isinstance(rhs, Signal) or isinstance(rhs, Constant):
                                if arg.type != at_filter_table[lhs.name][1][i]:
                                    status = False
                                    logger.error(f"{node.ln}: Atomic '{name}' malformed, left- and right-hand sides must be of same type (found '{arg.type}' and '{at_filter_table[lhs.name][1][i]}').\n\t{node}")
                                    return
                                
                                if isinstance(arg, Signal):
                                    if arg.name in program.signal_mapping:
                                        arg.sid = program.signal_mapping[arg.name]
                                    else:
                                        status = False
                                        logger.error(f'{arg.ln}: Signal \'{arg.name}\' not referenced in signal mapping.')
                            else:
                                status = False
                                logger.error(f"{node.ln}: Filter arguments must be signals or constants (found '{type(arg)}').\n\t{node}")
                        filter = lhs.name
                        filter_args = lhs.get_children()
                        lhs.type = at_filter_table[lhs.name][0]
                    else:
                        status = False
                        logger.error(f"{node.ln}: Atomic '{name}' malformed, filter '{lhs.name}' has incorrect number of arguments (expected {len(at_filter_table[lhs.name][1])}, found {len(lhs.get_children())}).\n\t{node}")
                        return
                else:
                    status = False
                    logger.error(f"{node.ln}: Atomic '{name}' malformed, filter '{lhs.name}' undefined.\n\t{node}")
                    return
            elif isinstance(lhs, Signal):
                if lhs.name in program.signal_mapping:
                    lhs.sid = program.signal_mapping[lhs.name]
                else:
                    status = False
                    logger.error(f'{lhs.ln}: Signal \'{lhs.name}\' not referenced in signal mapping.')

                filter = lhs.type.name
                filter_args = [lhs]
            elif not isinstance(lhs, Signal):
                status = False
                logger.error(f"{node.ln}: Atomic '{name}' malformed, expected filter or signal for left-hand side.\n\t{node}")
                return

            # type check right-hand side
            if isinstance(rhs, Signal) or isinstance(rhs, Constant):
                if lhs.type != rhs.type:
                    status = False
                    logger.error(f"{node.ln}: Atomic '{name}' malformed, left- and right-hand sides must be of same type (found '{lhs.type}' and '{rhs.type}').\n\t{node}")
                    return
                
                if isinstance(rhs, Signal):
                    if rhs.name in program.signal_mapping:
                        rhs.sid = program.signal_mapping[rhs.name]
                    else:
                        status = False
                        logger.error(f'{rhs.ln}: Signal \'{rhs.name}\' not referenced in signal mapping.')

            else:
                status = False
                logger.error(f"{node.ln}: Atomic '{name}' malformed, expected signal or constant for right-hand side.\n\t{node}")
                return

            return ATInstruction(node.ln, name, filter, filter_args, node, rhs)
        elif not isinstance(node, ATInstruction):
            status = False
            logger.error(f"{node.ln}: Atomic '{name}' malformed, expected relational operator at top-level.\n\t{node}")
            return
    
    # Type check FTSPEC
    formula_type = FormulaType.FT
    type_check_util(program.get_ft_specs())

    # Type check PTSPEC
    formula_type = FormulaType.PT
    type_check_util(program.get_pt_specs())

    # Type check atomics
    for name, expr in program.atomics.items():
        atomic: ATInstruction|None = type_check_atomic(name, expr)
        if atomic: 
            program.atomics[name] = atomic

    if status:
        program.is_type_correct = True

    return status


def insert_load_stores(program: Program) -> None:
    
    def insert_load_stores_util(node: Node) -> None:
        if isinstance(node, TLInstruction) and not isinstance(node, TLAtomicLoad):
            for child in node.get_children():
                if isinstance(child, BZInstruction):
                    child.replace(TLAtomicLoad(node.ln, deepcopy(child)))

    postorder(program, insert_load_stores_util)


def compute_scq_size(node: Node) -> int:
    """
    Computes SCQ sizes for each node in 'a' and returns the sum of each SCQ size. Sets this sum to the total_scq_size value of program.
    """
    visited: list[int] = []
    total: int = 0

    def compute_scq_size_util(node: Node) -> None:
        nonlocal visited
        nonlocal total

        if not isinstance(node, TLInstruction) or isinstance(node, Program):
            return

        if id(node) in visited:
            return
        visited.append(id(node))

        if isinstance(node, Specification):
            node.scq_size = 1
            total += node.scq_size
            return

        max_wpd: int = 0
        for p in node.get_parents():
            for s in p.get_children():
                if not id(s) == id(node):
                    max_wpd = s.wpd if s.wpd > max_wpd else max_wpd

        node.scq_size = max(max_wpd-node.bpd,0)+1 # works for +3 b/c of some bug -- ask Brian
        total += node.scq_size

    postorder(node, compute_scq_size_util)
    node.total_scq_size = total

    return total


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

    def rewrite_extended_operators_util(node: Node) -> None:

        if isinstance(node, LogicalOperator):
            if isinstance(node, LogicalOr):
                # p || q = !(!p && !q)
                node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [LogicalNegate(c.ln, c) for c in node.get_children()])))
            elif isinstance(node, LogicalXor):
                lhs: Node = node.get_lhs()
                rhs: Node = node.get_rhs()
                # p xor q = (p && !q) || (!p && q) = !(!(p && !q) && !(!p && q))
                node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [LogicalNegate(node.ln, \
                    LogicalAnd(node.ln, [lhs, LogicalNegate(rhs.ln, rhs)])), LogicalNegate(node.ln, \
                        LogicalAnd(node.ln, [LogicalNegate(lhs.ln, lhs), rhs]))])))
            elif isinstance(node, LogicalImplies):
                lhs: Node = node.get_lhs()
                rhs: Node = node.get_rhs()
                # p -> q = !(p && !q)
                node.replace(LogicalNegate(node.ln, LogicalAnd(lhs.ln, [lhs, LogicalNegate(rhs.ln, rhs)])))
            elif isinstance(node, LogicalIff):
                lhs: Node = node.get_lhs()
                rhs: Node = node.get_rhs()
                # p <-> q = !(p && !q) && !(p && !q)
                node.replace(LogicalAnd(node.ln, 
                    [LogicalNegate(node.ln, LogicalAnd(lhs.ln, [lhs, LogicalNegate(rhs.ln, rhs)])),
                     LogicalNegate(node.ln, LogicalAnd(lhs.ln, [LogicalNegate(lhs.ln, lhs), rhs]))])
                )
        elif isinstance(node, Release):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            bounds: Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(LogicalNegate(node.ln, Until(node.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))
        elif isinstance(node, Future):
            operand: Node = node.get_operand()
            bounds: Interval = node.interval
            # F p = True U p
            node.replace(Until(node.ln, Bool(node.ln, True), operand, bounds.lb, bounds.ub))

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

    def rewrite_boolean_normal_form_util(node: Node) -> None:

        if isinstance(node, LogicalOr):
            # p || q = !(!p && !q)
            node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [LogicalNegate(c.ln, c) for c in node.get_children()])))
        elif isinstance(node, LogicalImplies):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p -> q = !(p && !q)
            node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [lhs, LogicalNegate(rhs.ln, rhs)])))
        elif isinstance(node, LogicalXor):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p xor q = !(!p && !q) && !(p && q)
            node.replace(LogicalAnd(node.ln, [LogicalNegate(node.ln, LogicalAnd(lhs.ln, [LogicalNegate(lhs.ln, lhs), \
                LogicalNegate(rhs.ln, rhs)])), LogicalNegate(lhs.ln, LogicalAnd(lhs.ln, [lhs, rhs]))]))
        elif isinstance(node, Future):
            operand: Node = node.get_operand()
            bounds: Interval = node.interval
            # F p = True U p
            node.replace(Until(node.ln, Bool(operand.ln, True), operand, bounds.lb, bounds.ub))
        elif isinstance(node, Global):
            operand: Node = node.get_operand()
            bounds: Interval = node.interval
            # G p = !(True U !p)
            node.replace(LogicalNegate(node.ln, Until(node.ln, Bool(operand.ln, True), LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub)))
        elif isinstance(node, Release):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            bounds: Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(LogicalNegate(node.ln, Until(node.ln, LogicalNegate(lhs.ln, lhs), \
                                                      LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))

        for child in node.get_children():
            rewrite_boolean_normal_form_util(child)

    rewrite_boolean_normal_form_util(program)


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

    def rewrite_negative_normal_form_util(node: Node) -> None:

        if isinstance(node, LogicalNegate):
            operand = node.get_operand()
            if isinstance(operand, LogicalNegate):
                # !!p = p
                node.replace(operand.get_operand())
            if isinstance(operand, LogicalOr):
                # !(p || q) = !p && !q
                node.replace(LogicalAnd(node.ln, [LogicalNegate(c.ln, c) for c in operand.get_children()]))
            if isinstance(operand, LogicalAnd):
                # !(p && q) = !p || !q
                node.replace(LogicalOr(node.ln, [LogicalNegate(c.ln, c) for c in operand.get_children()]))
            elif isinstance(operand, Future):
                bounds: Interval = operand.interval
                # !F p = G !p
                node.replace(Global(node.ln, LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, Global):
                bounds: Interval = operand.interval
                # !G p = F !p
                node.replace(Future(node.ln, LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, Until):
                lhs: Node = operand.get_lhs()
                rhs: Node = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p U q) = !p R !q 
                node.replace(Release(node.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
            elif isinstance(operand, Release):
                lhs: Node = operand.get_lhs()
                rhs: Node = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p R q) = !p U !q
                node.replace(Until(node.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
        elif isinstance(node, LogicalImplies):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p -> q = !p || q
            node.replace(LogicalOr(node.ln, [LogicalNegate(lhs.ln, lhs), rhs]))
        elif isinstance(node, LogicalXor):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p xor q = (p && !q) || (!p && q)
            node.replace(LogicalOr(node.ln, [LogicalAnd(node.ln, [lhs, LogicalNegate(rhs.ln, rhs)]),\
                                       LogicalAnd(node.ln, [LogicalNegate(lhs.ln, lhs), rhs])]))

        for child in node.get_children():
            rewrite_negative_normal_form_util(child)

    rewrite_negative_normal_form_util(program)


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
    def rewrite_struct_access_util(node: Node) -> None:
        for c in node.get_children():
            rewrite_struct_access_util(c)

        if isinstance(node,StructAccess) and not isinstance(node.get_struct(),Variable):
            s: Struct = node.get_struct()
            node.replace(s.members[node.member])
    
    def rewrite_set_aggregation_util(a: Node) -> None:
        cur: Node = a

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

    def rewrite_struct_access_util(node: Node) -> None:
        if isinstance(node, StructAccess):
            s: Struct = node.get_struct()
            node.replace(s.members[node.member])

    postorder(program, rewrite_struct_access_util)
    program.is_struct_access_free = True


def optimize_rewrite_rules(program: Node) -> None:

    def optimize_rewrite_rules_util(node: Node) -> None:
        if isinstance(node, LogicalNegate):
            opnd1 = node.get_operand()
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # !true = false
                    node.replace(Bool(node.ln, False))
                else:
                    # !false = true
                    node.replace(Bool(node.ln, True))
            elif isinstance(opnd1, LogicalNegate):
                # !!p = p
                node.replace(opnd1.get_operand())
            elif isinstance(opnd1, Global):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    node.replace(Future(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
            elif isinstance(opnd1, Future):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    node.replace(Global(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
        elif isinstance(node, Equal):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(lhs, Bool) and isinstance(rhs, Bool):
                pass
            elif isinstance(lhs, Bool):
                # (true == p) = p
                node.replace(rhs)
            elif isinstance(rhs, Bool):
                # (p == true) = p
                node.replace(lhs)
        elif isinstance(node, Global):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # G[0,0]p = p
                node.replace(opnd1)
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # G[l,u]True = True
                    node.replace(Bool(node.ln, True))
                else:
                    # G[l,u]False = False
                    node.replace(Bool(node.ln, False))
            elif isinstance(opnd1, Global):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                node.replace(Global(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, Future):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    node.replace(Future(node.ln, opnd2, lb, ub))
        elif isinstance(node, Future):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # F[0,0]p = p
                node.replace(opnd1)
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # F[l,u]True = True
                    node.replace(Bool(node.ln, True))
                else:
                    # F[l,u]False = False
                    node.replace(Bool(node.ln, False))
            elif isinstance(opnd1, Future):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                node.replace(Future(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, Global):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    node.replace(Global(node.ln, opnd2, lb, ub))
        elif isinstance(node, LogicalAnd):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
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
                        node.replace(Global(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        node.replace(Global(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        node.replace(Global(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        node.replace(Global(node.ln, p, lb2, max(ub1,ub2)))
                        return

                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                node.replace(Global(node.ln, LogicalAnd(node.ln, 
                        [Global(node.ln, p, lb1-lb3, ub1-ub3), Global(node.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
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
                        node.replace(Future(node.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        node.replace(Future(node.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    node.replace(Until(node.ln, LogicalAnd(node.ln, [lhs_lhs, rhs_lhs]), lhs_rhs, lhs.interval.lb, 
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(node, LogicalOr):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
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
                        node.replace(Future(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        node.replace(Future(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        node.replace(Future(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        node.replace(Future(node.ln, p, lb2, max(ub1,ub2)))
                        return

                # TODO: check for when lb==ub==0
                # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                node.replace(Future(node.ln, LogicalOr(node.ln, 
                        [Future(node.ln, p, lb1-lb3, ub1-ub3), Future(node.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
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
                        node.replace(Global(node.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        node.replace(Global(node.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    node.replace(Until(node.ln, LogicalOr(node.ln, [lhs_rhs, rhs_rhs]), lhs_lhs, lhs.interval.lb, 
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(node, Until):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(rhs, Global) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                node.replace(Global(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))
            elif isinstance(rhs, Future) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                node.replace(Future(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))

    postorder(program, optimize_rewrite_rules_util)


def optimize_stratify_associative_operators(node: Node) -> None:
    """TODO"""
    
    def optimize_associative_operators_rec(node: Node) -> None:
        if isinstance(node, LogicalAnd) and len(node.get_children()) > 2:
            n: int = len(node.get_children())
            children = [c for c in node.get_children()]
            wpds = [c.wpd for c in children]
            wpds.sort(reverse=True)

            T = max(children, key=lambda c: c.wpd)

            if (n-2)*(wpds[0]-wpds[1])-wpds[2]+min([c.bpd for c in node.get_children() if c.wpd < wpds[0]]):
                node.replace(LogicalAnd(node.ln, [LogicalAnd(node.ln, [c for c in children if c != children[0]]), children[0]]))
                children[0].get_parents().remove(node)

        elif isinstance(node, LogicalOr):
            max_wpd: int = max([c.wpd for c in node.get_children()])
            target: Node = next(c for c in node.get_children() if c.wpd == max_wpd)

            new_children = [c for c in node.get_children() if c != target]
            new_ast = LogicalOr(node.ln, [LogicalOr(node.ln, new_children), target])

            if compute_scq_size(new_ast) < compute_scq_size(node):
                # (a0 && a1 && ... && an) = ((a1 && a2 && ... && an-1) && an)
                node.replace(new_ast)

        for c in node.get_children():
            optimize_associative_operators_rec(c)

    optimize_associative_operators_rec(node)


def rewrite_contracts(program: Program) -> None:
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""

    for spec_set in program.get_children():
        for contract in [c for c in spec_set.get_children() if isinstance(c, Contract)]:
            spec_set.remove_child(contract)

            spec_set.add_child(Specification(
                contract.ln, 
                contract.name, 
                contract.formula_numbers[0], 
                contract.get_assumption()
            ))

            spec_set.add_child(Specification(
                contract.ln, 
                contract.name, 
                contract.formula_numbers[1], 
                LogicalImplies(contract.ln, contract.get_assumption(), contract.get_guarantee())
            ))

            spec_set.add_child(Specification(
                contract.ln, 
                contract.name, 
                contract.formula_numbers[2], 
                LogicalAnd(contract.ln, [contract.get_assumption(), contract.get_guarantee()])
            ))

            program.contracts[contract.name] = contract.formula_numbers


def optimize_cse(program: Program) -> None:
    """
    Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence. Applies CSE to FT/PT formulas separately.

    Preconditions:
        - program is type correct.

    Postconditions:
        - Sets of FT/PT specifications have no distinct, syntactically equivalent sub-expressions (i.e., is CSE reduced).
        - Some nodes in AST may have multiple parents.
    """
    
    if not program.is_type_correct:
        logger.error(f' Program must be type checked before CSE.')
        return

    S: dict[str, Node]
    
    def optimize_cse_util(node: Node) -> None:
        nonlocal S

        if str(node) in S:
            node.replace(S[str(node)])
        else:
            S[str(node)] = node

    S = {}
    postorder(program.get_ft_specs(), optimize_cse_util)

    S = {}
    postorder(program.get_pt_specs(), optimize_cse_util)
    
    program.is_cse_reduced = True


def generate_alias(program: Program) -> str:
    """
    Generates string corresponding to the alias file for the argument program. The alias file is used by R2U2 to print formula labels and contract status.

    Preconditions:
        - program is type correct

    Postconditions:
        - None
    """
    s: str = ''

    specs = [s for s in program.get_ft_specs().get_children() + program.get_pt_specs().get_children()]

    for spec in specs:
        if spec.name in program.contracts: 
            # then formula is part of contract, ignore
            continue
        if isinstance(spec, Specification):
            s += f"F {spec.name} {spec.formula_number}\n"

    for label,fnums in program.contracts.items():
        s += f"C {label} {fnums[0]} {fnums[1]} {fnums[2]}\n"

    return s


def generate_at_assembly(program: Program) -> list[ATInstruction]:
    asm: list[ATInstruction] = []
    
    for name,atomic in program.atomics.items():
        if atomic.atid < 0:
            logger.warning(f"{atomic.ln}: Unused atomic '{name}'.")
        elif isinstance(atomic, ATInstruction):
            asm.append(atomic)
        else:
            logger.error(f" Internal error resolving atomics.")

    return asm


def generate_assembly(program: Program, at: bool, bz: bool) -> dict[FormulaType, list[Instruction]]:
    visited: set[Node] = set()
    asm: dict[FormulaType, list[Instruction]] = {}
    formula_type: FormulaType
    tlid: int = 0
    atid: int = 0

    asm[FormulaType.FT] = []
    asm[FormulaType.PT] = []

    def assign_ids(ast: Node) -> None:
        nonlocal tlid, atid

        if ast in visited:
            return
        visited.add(ast)
        
        if isinstance(ast, TLInstruction):
            ast.tlid = tlid
            tlid += 1
        
        if isinstance(ast, BZInstruction):
            ast.atid = atid
            atid += 1

        if isinstance(ast, ATInstruction):
            pass
        



    def assign_ids_util(node: Node) -> None:
        nonlocal visited
        nonlocal tlid
        nonlocal atid

        if isinstance(node, Bool) or node in visited:
            return
        visited.add(node)

        if isinstance(node, TLInstruction):
            node.tlid = tlid
            tlid += 1

        if isinstance(node, Atomic):
            node.atid = program.signal_mapping[node.name]

    def generate_assembly_util(node: Node) -> None:
        nonlocal visited
        nonlocal asm
        nonlocal formula_type

        if isinstance(node, Bool):
            return
        elif isinstance(node,TLInstruction):
            if not node in visited:
                asm[formula_type].append(node)
                visited.add(node)
        else:
            logger.error(f'{node.ln}: Invalid node type for assembly generation ({type(node)})')

    def assign_ids_at_util(node: Node) -> None:
        nonlocal visited
        nonlocal tlid
        nonlocal atid

        if isinstance(node, Bool) or node in visited:
            return
        visited.add(node)

        if isinstance(node, TLInstruction):
            node.tlid = tlid
            tlid += 1

        if isinstance(node, Atomic):
            if program.atomics[node.name].atid > -1:
                node.atid = program.atomics[node.name].atid
            else:
                node.atid = atid
                program.atomics[node.name].atid = atid
                atid += 1

    def generate_assembly_at_util(node: Node) -> None:
        nonlocal visited
        nonlocal asm
        nonlocal formula_type

        if isinstance(node, Bool):
            return
        elif isinstance(node,TLInstruction):
            if not node in visited:
                asm[formula_type].append(node)
                visited.add(node)
        else:
            logger.error(f'{node.ln}: Invalid node type for assembly generation ({type(node)})')

    def assign_ids_bz_util(node: Node) -> None:
        nonlocal visited
        nonlocal tlid
        nonlocal atid

        if isinstance(node, Bool) or node in visited:
            return
        visited.add(node)

        if isinstance(node, TLInstruction):
            node.tlid = tlid
            tlid += 1
            
            if isinstance(node, TLAtomicLoad):
                node.get_load().atid = atid
                atid += 1

    def generate_assembly_bz_util(node: Node) -> None:
        nonlocal visited
        nonlocal asm

        if isinstance(node, Bool):
            return
        elif isinstance(node, TLInstruction):
            if not node in visited:
                asm[formula_type].append(node)
                visited.add(node)
        elif isinstance(node, BZInstruction):
            asm[formula_type].append(node)
            visited.add(node)
        else:
            logger.error(f'{node.ln}: Invalid node type for assembly generation ({type(node)})')

    if at:
        tlid = 0
        formula_type = FormulaType.FT
        postorder(program.get_ft_specs(), assign_ids_at_util)
        visited = set()
        postorder(program.get_ft_specs(), generate_assembly_at_util)

        tlid = 0
        formula_type = FormulaType.PT
        visited = set()
        postorder(program.get_pt_specs(), assign_ids_at_util)
        visited = set()
        postorder(program.get_pt_specs(), generate_assembly_at_util)
    elif bz:
        tlid = 0
        formula_type = FormulaType.FT
        postorder(program.get_ft_specs(), assign_ids_bz_util)
        visited = set()
        postorder(program.get_ft_specs(), generate_assembly_bz_util)
        
        tlid = 0
        formula_type = FormulaType.PT
        visited = set()
        postorder(program.get_pt_specs(), assign_ids_bz_util)
        visited = set()
        postorder(program.get_pt_specs(), generate_assembly_bz_util)
    else:
        tlid = 0
        formula_type = FormulaType.FT
        postorder(program.get_ft_specs(), assign_ids_util)
        visited = set()
        postorder(program.get_ft_specs(), generate_assembly_util)
        
        tlid = 0
        formula_type = FormulaType.PT
        visited = set()
        postorder(program.get_pt_specs(), assign_ids_util)
        visited = set()
        postorder(program.get_pt_specs(), generate_assembly_util)

    return asm


def generate_scq_assembly(program: Program) -> list[tuple[int,int]]:
    ret: list[tuple[int,int]] = []
    pos: int = 0
    explored: list[Node] = []

    compute_scq_size(program.get_ft_specs())

    def gen_scq_assembly_util(a: Node) -> None:
        nonlocal ret
        nonlocal pos
        nonlocal explored

        if a in explored:
            return

        if not isinstance(a,TLInstruction) or isinstance(a,Program):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        ret.append((start_pos,end_pos))

        explored.append(a)

    postorder(program.get_ft_specs(), gen_scq_assembly_util)
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

    def compute_cpu_wcet_util(a: Node) -> int:
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

    def compute_fpga_wcet_util(a: Node) -> float:
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


def parse(input: str) -> Program|None:
    lexer: C2POLexer = C2POLexer()
    parser: C2POParser = C2POParser()
    specs: dict[FormulaType, SpecificationSet] = parser.parse(lexer.tokenize(input))

    if not parser.status:
        return None

    if not FormulaType.FT in specs:
        specs[FormulaType.FT] = SpecificationSet(0, FormulaType.FT, [])

    if not FormulaType.PT in specs:
        specs[FormulaType.PT] = SpecificationSet(0, FormulaType.PT, [])

    return Program(
        0, 
        parser.structs, 
        parser.atomics, 
        specs[FormulaType.FT], 
        specs[FormulaType.PT]
    )


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
        program: Program|None = parse(f.read())

    if not program:
        logger.error(' Failed parsing.')
        return ReturnCode.PARSE_ERROR.value

    # parse csv/signals file
    program.signal_mapping = parse_signals(signals_filename)

    # type check
    if not type_check(program, at, bz):
        logger.error(' Failed type check.')
        return ReturnCode.TYPE_CHECK_ERROR.value

    if bz:
        insert_load_stores(program)

    rewrite_contracts(program)
    rewrite_set_aggregation(program)
    rewrite_struct_access(program)

    # rewrite without extended operators if enabled
    if not extops:
        rewrite_extended_operators(program)

    optimize_rewrite_rules(program)

    # common sub-expressions elimination
    if cse:
        optimize_cse(program)

    # generate alias file
    alias = generate_alias(program)

    # generate assembly
    asm: dict[FormulaType, list[Instruction]] = generate_assembly(program, at, bz)
    at_asm: list[ATInstruction] = generate_at_assembly(program)
    scq_asm: list[tuple[int,int]] = generate_scq_assembly(program)

    if bz and (not validate_booleanizer_stack(asm[FormulaType.FT]) or not validate_booleanizer_stack(asm[FormulaType.PT])):
        logger.error(f' Internal error: Booleanizer stack size potentially invalid during execution.')
        return ReturnCode.ASM_ERROR.value

    # print asm if 'quiet' option not enabled
    if not quiet:
        if at:
            print(Color.HEADER+'AT Assembly'+Color.ENDC+':')
            for s in at_asm:
                print(f"\t{s.asm()}")
        print(Color.HEADER+'FT Assembly'+Color.ENDC+':')
        for a in asm[FormulaType.FT]:
            print(f"\t{a.asm()}")
        print(Color.HEADER+'PT Assembly'+Color.ENDC+':')
        for a in asm[FormulaType.PT]:
            print(f"\t{a.asm()}")
        print(Color.HEADER+'SCQ Assembly'+Color.ENDC+':')
        for s in scq_asm:
            print(f"\t{s}")

    return ReturnCode.SUCCESS.value

