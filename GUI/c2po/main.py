from __future__ import annotations
import contextlib
import io
from typing import Dict, List, Tuple
import inspect
import sys
from logging import getLogger
# from time import perf_counter

from .logger import *
from .ast import *
from .rewrite import *
from .parser import C2POLexer
from .parser import C2POParser
from .assembler import assemble


logger = getLogger(STANDARD_LOGGER_NAME)


class ReturnCode(Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERROR = 2
    TYPE_CHECK_ERROR = 3
    ASM_ERROR = 4
    INVALID_OPTIONS = 5

COMPILE_ERR_RETURN_VAL: Callable[[int], tuple[int, List[TLInstruction], List[TLInstruction], List[BZInstruction], List[ATInstruction], List[Tuple[int,int]]]] = lambda rc: (rc,[],[],[],[],[])


# Stores the sub-classes of Instruction from ast.py
instruction_list = [cls for (name,cls) in inspect.getmembers(sys.modules["c2po.ast"],
        lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction))]

default_cpu_latency_table: Dict[str, int] = { name:10 for (name,value) in
    inspect.getmembers(sys.modules["c2po.ast"],
        lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction) and
            obj != Instruction and
            obj != TLInstruction and
            obj != BZInstruction) }

default_fpga_latency_table: Dict[str, Tuple[float,float]] = { name:(10.0,10.0) for (name,value) in
    inspect.getmembers(sys.modules["c2po.ast"],
        lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction) and
            obj != Instruction and
            obj != TLInstruction and
            obj != BZInstruction) }

AT_FILTER_TABLE: Dict[str, Tuple[List[Type], Type]] = {
    "rate": ([FLOAT(False)], FLOAT(False)),
    "movavg": ([FLOAT(False),INT(True)], FLOAT(False)),
    "abs_diff_angle": ([FLOAT(False),FLOAT(True)], FLOAT(False))
}


def collect_signals(program: Program) -> Dict[str,int]:
    mapping: Dict[str,int] = {}
    sid: int = 0

    for signal in program.signals:
        mapping[signal] = sid
        sid += 1

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
    explored: List[Node] = []
    context: Dict[str,Type] = {}
    st: StructDict = program.structs
    formula_type: FormulaType = FormulaType.PROP
    in_parameterized_set_agg: bool = False

    def resolve_variables_util(node: Node) -> None:
        """Recursively replace any Variable instances to Atomic, Signal, or definitions, unless it is a set aggregation variable."""
        nonlocal status

        if isinstance(node, Variable):
            if node.name in program.atomics:
                if program.implementation != R2U2Implementation.C:
                    status = False
                    logger.error(f"{node.ln}: Atomics only support in C version of R2U2.\n\t{node}")
                if not at:
                    status = False
                    logger.error(f"{node.ln}: Atomic '{node.name}' referenced, but atomic checker disabled.")

                node.replace(Atomic(node.ln, node.name))
            elif node.name in program.signals:
                if at:
                    if not node.name in program.signal_mapping:
                        status = False
                        logger.error(f"{node.ln}: Non-Boolean signals not allowed in specifications when AT enabled.\n\t{node}")

                    sig = Signal(node.ln, node.name, program.signals[node.name])
                    sig.sid = program.signal_mapping[sig.name]
                    one = Integer(sig.ln, 1)
                    a_copy = deepcopy(sig)
                    instr = ATInstruction(sig.ln, sig.name, "int", [a_copy], Equal(sig.ln, a_copy, one), one)
                    program.atomics[sig.name] = instr
                    node.replace(Atomic(sig.ln, sig.name))
                else:
                    if not node.name in program.signal_mapping:
                        status = False
                        logger.error(f'{node.ln}: Signal \'{node}\' not referenced in signal mapping.')

                    sig = Signal(node.ln, node.name, program.signals[node.name])
                    sig.sid = program.signal_mapping[sig.name]
                    node.replace(sig)
            elif node.name in context:
                pass
            elif node.name in program.definitions:
                define = program.definitions[node.name]
                if isinstance(define, Specification):
                    node.replace(define.get_expr())
                else:
                    node.replace(define)
            else:
                status = False
                logger.error(f"{node.ln}: Variable '{node}' not recognized.")
        elif isinstance(node, SetAggOperator):
            context[node.get_boundvar().name] = node.get_boundvar().type
            resolve_variables_util(node.get_set())
            resolve_variables_util(node.get_expr())
            if isinstance(node, ForExactlyN) or isinstance(node, ForAtLeastN) or isinstance(node, ForAtMostN):
                resolve_variables_util(node.get_num())
            del context[node.get_boundvar().name]
        else:
            for child in node.get_children():
                resolve_variables_util(child)

    def type_check_util(node: Node) -> None:
        nonlocal formula_type
        nonlocal status
        nonlocal in_parameterized_set_agg

        node.formula_type = formula_type

        if isinstance(node, Constant):
            return
        elif isinstance(node, Signal):
            return
        elif isinstance(node, Atomic):
            return
        elif isinstance(node, Variable):
            node.type = context[node.name]
        elif isinstance(node, SpecificationSet):
            for c in node.get_children():
                type_check_util(c)
        elif isinstance(node,Specification):
            child = node.get_expr()
            type_check_util(child)

            if not child.type == BOOL(False):
                status = False
                logger.error(f'{node.ln}: Specification must be of boolean type (found \'{child.type}\')\n\t{node}')
        elif isinstance(node, Contract):
            if program.implementation != R2U2Implementation.C:
                status = False
                logger.error(f"{node.ln}: Contracts only support in C version of R2U2.\n\t{node}")

            assume: TLInstruction = node.get_assumption()
            guarantee: TLInstruction = node.get_guarantee()

            type_check_util(assume)
            type_check_util(guarantee)

            if not assume.type == BOOL(False):
                status = False
                logger.error(f'{node.ln}: Assumption must be of boolean type (found \'{assume.type}\')\n\t{node}')

            if not guarantee.type == BOOL(False):
                status = False
                logger.error(f'{node.ln}: Guarantee must be of boolean type (found \'{guarantee.type}\')\n\t{node}')

            node.type = BOOL(assume.type.is_const and guarantee.type.is_const)
        elif isinstance(node, Function):
            status = False
            logger.error(f"{node.ln}: Functions unsupported.\n\t{node}")
        elif isinstance(node, RelationalOperator):
            if program.implementation != R2U2Implementation.C:
                status = False
                logger.error(f"{node.ln}: Relational operators only support in C version of R2U2.\n\t{node}")

            lhs = node.get_lhs()
            rhs = node.get_rhs()
            type_check_util(lhs)
            type_check_util(rhs)

            if lhs.type != rhs.type:
                status = False
                logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', must be of same type (found \'{lhs.type}\' and \'{rhs.type}\')\n\t{node}')

            node.type = BOOL(lhs.type.is_const and rhs.type.is_const)
        elif isinstance(node, ArithmeticOperator):
            is_const: bool = True

            if program.implementation != R2U2Implementation.C:
                status = False
                logger.error(f"{node.ln}: Arithmetic operators only support in C version of R2U2.\n\t{node}")

            if not bz:
                status = False
                logger.error(f'{node.ln}: Found BZ expression, but Booleanizer expressions disabled\n\t{node}')

            for c in node.get_children():
                type_check_util(c)
                is_const = is_const and c.type.is_const
            t: Type = node.get_child(0).type
            t.is_const = is_const

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
            is_const: bool = True

            if program.implementation != R2U2Implementation.C:
                status = False
                logger.error(f"{node.ln}: Bitwise operators only support in C version of R2U2.\n\t{node}")

            if not bz:
                status = False
                logger.error(f'{node.ln}: Found BZ expression, but Booleanizer expressions disabled\n\t{node}')

            t: Type = NOTYPE()
            for c in node.get_children():
                type_check_util(c)
                is_const = is_const and c.type.is_const
                t = c.type
            t.is_const = is_const

            for c in node.get_children():
                if c.type != t or not is_integer_type(c.type):
                    status = False
                    logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', found \'{c.type}\' (\'{c}\') but expected \'{node.get_child(0).type}\'\n\t{node}')

            node.type = t
        elif isinstance(node, LogicalOperator):
            is_const: bool = True

            for c in node.get_children():
                type_check_util(c)
                is_const = is_const and c.type.is_const
                if c.type != BOOL(False):
                    status = False
                    logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{node}')

            node.type = BOOL(is_const)
        elif isinstance(node, TemporalOperator):
            is_const: bool = True

            for c in node.get_children():
                type_check_util(c)
                is_const = is_const and c.type.is_const
                if c.type != BOOL(False):
                    status = False
                    logger.error(f'{node.ln}: Invalid operands for \'{node.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{node}')

            # check for mixed-time formulas
            if isinstance(node, FutureTimeOperator):
                if formula_type == FormulaType.PT:
                    status = False
                    logger.error(f'{node.ln}: Mixed-time formulas unsupported, found FT formula in PTSPEC.\n\t{node}')
            elif isinstance(node, PastTimeOperator):
                if program.implementation != R2U2Implementation.C:
                    status = False
                    logger.error(f"{node.ln}: Past-time operators only support in C version of R2U2.\n\t{node}")
                if formula_type == FormulaType.FT:
                    status = False
                    logger.error(f'{node.ln}: Mixed-time formulas unsupported, found PT formula in FTSPEC.\n\t{node}')

            if node.interval.lb > node.interval.ub:
                status = status
                logger.error(f'{node.ln}: Time interval invalid, lower bound must less than or equal to upper bound (found [{node.interval.lb},{node.interval.ub}])')

            node.type = BOOL(is_const)
        elif isinstance(node,Set):
            t: Type = NOTYPE()
            is_const: bool = True

            for m in node.get_children():
                type_check_util(m)
                is_const = is_const and m.type.is_const
                t = m.type

            for m in node.get_children():
                if m.type != t:
                    status = False
                    logger.error(f'{node.ln}: Set \'{node}\' must be of homogeneous type (found \'{m.type}\' and \'{t}\')')

            node.type = SET(is_const, t)
        elif isinstance(node, SetAggOperator):
            s: Set = node.get_set()
            boundvar: Variable = node.get_boundvar()

            type_check_util(s)

            if isinstance(s.type, SET):
                context[boundvar.name] = s.type.member_type
            else:
                status = False
                logger.error(f'{node.ln}: Set aggregation set must be Set type (found \'{s.type}\')')

            if isinstance(node, ForExactlyN) or isinstance(node, ForAtLeastN) or isinstance(node, ForAtMostN):
                in_parameterized_set_agg = True
                if not bz:
                    status = False
                    logger.error(f'{node.ln}: Parameterized set aggregation operators require Booleanizer, but Booleanizer not enabled.')

                n: Node = node.get_num()
                type_check_util(n)
                if not is_integer_type(n.type):
                    status = False
                    logger.error(f'{node.ln}: Parameter for set aggregation must be integer type (found \'{n.type}\')')

            expr: Node = node.get_expr()
            type_check_util(expr)

            if expr.type != BOOL(False):
                status = False
                logger.error(f"{node.ln}: Set aggregation expression must be 'bool' (found '{expr.type}')")

            del context[boundvar.name]
            if boundvar in explored:
                explored.remove(boundvar)

            node.type = BOOL(expr.type.is_const and s.type.is_const)
            in_parameterized_set_agg = False
        elif isinstance(node, Struct):
            is_const: bool = True

            for member in node.get_children():
                type_check_util(member)
                is_const = is_const and member.type.is_const

            for (m,t) in st[node.name]:
                if node.get_member(m).type != t:
                    logger.error(f'{node.ln}: Member \'{m}\' invalid type for struct \'{node.name}\' (expected \'{t}\' but got \'{node.get_member(m).type}\')')

            node.type = STRUCT(is_const, node.name)
        elif isinstance(node, StructAccess):
            type_check_util(node.get_struct())

            st_name = node.get_struct().type.name
            if st_name in st.keys():
                valid_member: bool = False
                for (m,t) in st[st_name]:
                    if node.member == m:
                        node.type = t
                        valid_member = True
                if not valid_member:
                    status = False
                    logger.error(f'{node.ln}: Member \'{node.member}\' invalid for struct \'{node.get_struct().name}\'')
            else:
                status = False
                logger.error(f'{node.ln}: Member \'{node.member}\' invalid for struct \'{node.get_struct().name}\'')
        else:
            logger.error(f'{node.ln}: Invalid expression\n\t{node}')
            status = False

        if isinstance(node, TLInstruction) and in_parameterized_set_agg:
            status = False
            logger.error(f'{node.ln}: Parameterized set aggregation expressions only accept Booleanizer operators.\n\tConsider using bit-wise operators in place of logical operators.\n\t{node}')

    def type_check_atomic(name: str, node: Node) -> ATInstruction|None:
        nonlocal status

        if isinstance(node, RelationalOperator):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()

            filter: str = ""
            filter_args: List[Node] = []

            # type check left-hand side
            if isinstance(lhs, Function):
                if not lhs.name in AT_FILTER_TABLE:
                    status = False
                    logger.error(f"{node.ln}: Atomic '{name}' malformed, filter '{lhs.name}' undefined.\n\t{node}")
                    return

                if not len(AT_FILTER_TABLE[lhs.name][0]) == len(lhs.get_children()):
                    status = False
                    logger.error(f"{node.ln}: Atomic '{name}' malformed, filter '{lhs.name}' has incorrect number of arguments (expected {len(AT_FILTER_TABLE[lhs.name][0])}, found {len(lhs.get_children())}).\n\t{node}")
                    return

                for i in range(0, len(lhs.get_children())):
                    arg: Node = lhs.get_child(i)

                    if isinstance(arg, Variable):
                        if arg.name in program.signals:
                            sig = Signal(arg.ln, arg.name, program.signals[arg.name])
                            if arg.name in program.signal_mapping:
                                sig.sid = program.signal_mapping[arg.name]
                                arg.replace(sig)
                            else:
                                status = False
                                logger.error(f'{arg.ln}: Signal \'{arg.name}\' not referenced in signal mapping.')

                            if sig.type != AT_FILTER_TABLE[lhs.name][0][i]:
                                status = False
                                logger.error(f"{node.ln}: Atomic '{name}' malformed, left- and right-hand sides must be of same type (found '{sig.type}' and '{AT_FILTER_TABLE[lhs.name][0][i]}').\n\t{node}")
                                return
                    elif isinstance(arg, Constant):
                        if arg.type != AT_FILTER_TABLE[lhs.name][0][i]:
                            status = False
                            logger.error(f"{node.ln}: Atomic '{name}' malformed, left- and right-hand sides must be of same type (found '{arg.type}' and '{AT_FILTER_TABLE[lhs.name][0][i]}').\n\t{node}")
                            return
                    else:
                        status = False
                        logger.error(f"{node.ln}: Filter arguments must be signals or constants (found '{type(arg)}').\n\t{node}")

                filter = lhs.name
                filter_args = lhs.get_children()
                lhs.type = AT_FILTER_TABLE[lhs.name][1]
            elif isinstance(lhs, Variable):
                if lhs.name in program.signals:
                    sig = Signal(lhs.ln, lhs.name, program.signals[lhs.name])
                    if lhs.name in program.signal_mapping:
                        sig.sid = program.signal_mapping[lhs.name]
                        lhs.replace(sig)
                        lhs.type = sig.type
                    else:
                        status = False
                        logger.error(f'{lhs.ln}: Signal \'{lhs.name}\' not referenced in signal mapping.')

                    filter = sig.type.name
                    filter_args = [sig]
                elif lhs.name in program.definitions and isinstance(program.definitions[lhs.name], Specification):
                    lhs.replace(program.definitions[lhs.name])
                    filter = "formula"
                    filter_args = [program.definitions[lhs.name]]
                    lhs.type = BOOL(False)
            else:
                status = False
                logger.error(f"{node.ln}: Atomic '{name}' malformed, expected filter or signal for left-hand side.\n\t{node}")
                return

            # type check right-hand side
            if isinstance(rhs, Variable):
                if not rhs.name in program.signals:
                    status = False
                    logger.error(f'{rhs.ln}: Signal \'{rhs.name}\' not declared.')

                if not rhs.name in program.signal_mapping:
                    status = False
                    logger.error(f'{rhs.ln}: Signal \'{rhs.name}\' not referenced in signal mapping.')

                if program.signals[rhs.name] != lhs.type:
                    status = False
                    logger.error(f"{node.ln}: 1 Atomic '{name}' malformed, left- and right-hand sides must be of same type (found '{lhs.type}' and '{rhs.type}').\n\t{node}")
                    return

                sig = Signal(rhs.ln, rhs.name, program.signals[rhs.name])
                sig.sid = program.signal_mapping[sig.name]
                rhs.replace(sig)
                rhs = sig
            elif isinstance(rhs, Constant):
                if lhs.type != rhs.type:
                    status = False
                    logger.error(f"{node.ln}: Atomic '{name}' malformed, left- and right-hand sides must be of same type (found '{lhs.type}' and '{rhs.type}').\n\t{node}")
                    return
            else:
                status = False
                logger.error(f"{node.ln}: Atomic '{name}' malformed, expected signal or constant for right-hand side.\n\t{node}")
                return

            return ATInstruction(node.ln, name, filter, filter_args, node, rhs)
        elif not isinstance(node, ATInstruction):
            status = False
            logger.error(f"{node.ln}: Atomic '{name}' malformed, expected relational operator at top-level.\n\t{node}")
            return

    resolve_variables_util(program)
    explored = []

    for definition in [d for d in program.definitions.values() if not isinstance(d, Specification)]:
        resolve_variables_util(definition)
        type_check_util(definition)

    # Type check atomics
    for name, expr in program.atomics.items():
        atomic: ATInstruction|None = type_check_atomic(name, expr)
        if atomic:
            program.atomics[name] = atomic
        
    # Type check FTSPEC
    formula_type = FormulaType.FT
    type_check_util(program.get_ft_specs())

    # Type check PTSPEC
    formula_type = FormulaType.PT
    type_check_util(program.get_pt_specs())

    if status:
        program.is_type_correct = True

    return status


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

    S: Dict[str, Node]

    def optimize_cse_util(node: Node) -> None:
        nonlocal S

        if str(node) in S:
            node.replace(S[str(node)])
        else:
            S[str(node)] = node

    S = {}
    postorder_iterative(program.get_ft_specs(), optimize_cse_util)

    S = {k:v for (k,v) in S.items() if isinstance(v, BZInstruction)}
    postorder_iterative(program.get_pt_specs(), optimize_cse_util)

    program.is_cse_reduced = True


def generate_aliases(program: Program) -> List[str]:
    """
    Generates strings corresponding to the alias file for the argument program. The alias file is used by R2U2 to print formula labels and contract status.

    Preconditions:
        - program is type correct

    Postconditions:
        - None
    """
    s: List[str] = []

    specs = [s for s in program.get_ft_specs().get_children() + program.get_pt_specs().get_children()]

    for spec in specs:
        if spec.name in program.contracts:
            # then formula is part of contract, ignore
            continue
        if isinstance(spec, Specification):
            s.append(f"F {spec.name} {spec.formula_number}")

    for label,fnums in program.contracts.items():
        s.append(f"C {label} {fnums[0]} {fnums[1]} {fnums[2]}")

    return s


def generate_assembly(program: Program, at: bool, bz: bool) -> Tuple[List[TLInstruction], List[TLInstruction], List[BZInstruction], List[ATInstruction]]:
    formula_type: FormulaType
    ftid: int = 0
    ptid: int = 0
    bzid: int = 0
    atid: int = 0

    ft_asm = []
    pt_asm = []
    bz_asm = []
    at_asm = []

    def assign_ftids(node: Node) -> None:
        nonlocal ftid, bzid, atid

        if isinstance(node, TLInstruction):
            node.ftid = ftid
            ftid += 1

        if isinstance(node, BZInstruction):
            if node.bzid < 0:
                node.bzid = bzid
                bzid += 1

            if node.has_tl_parent():
                node.ftid = ftid
                ftid += 1
                if node.atid < 0:
                    node.atid = atid
                    atid += 1

        if isinstance(node, Atomic):
            # Retrieve cached atomic number from program.atomics, assign from
            # atid counter on first lookup
            #
            # Key exception possible if atomic node does not appear in atomics
            if program.atomics[node.name].atid == -1:
                node.atid = atid
                program.atomics[node.name].atid = atid
                atid += 1
            else:
                node.atid = program.atomics[node.name].atid

    def assign_ptids(node: Node) -> None:
        nonlocal ptid, bzid, atid

        if isinstance(node, TLInstruction):
            node.ptid = ptid
            ptid += 1

        if isinstance(node, BZInstruction):
            if node.bzid < 0:
                node.bzid = bzid
                bzid += 1

            if node.has_tl_parent():
                node.ptid = ptid
                ptid += 1
                if node.atid < 0:
                    node.atid = atid
                    atid += 1

        if isinstance(node, Atomic):
            # Retrieve cached atomic number from program.atomics, assign from
            # atid counter on first lookup
            #
            # Key exception possible if atomic node does not appear in atomics
            if program.atomics[node.name].atid == -1:
                node.atid = atid
                program.atomics[node.name].atid = atid
                atid += 1
            else:
                node.atid = program.atomics[node.name].atid


    def generate_assembly_util(node: Node) -> None:
        nonlocal formula_type

        if isinstance(node, Instruction):
            if formula_type == FormulaType.FT and node.ftid > -1:
                ft_asm.append(node)
            elif formula_type == FormulaType.PT and node.ptid > -1:
                pt_asm.append(node)
            if node.bzid > -1 and not node in bz_asm:
                bz_asm.append(node)
        elif not isinstance(node, Bool):
            logger.critical(f" Invalid node type for assembly generation (found '{type(node)}').")

    postorder_iterative(program.get_ft_specs(), assign_ftids)
    postorder_iterative(program.get_pt_specs(), assign_ptids)

    formula_type = FormulaType.FT
    postorder_iterative(program.get_ft_specs(), generate_assembly_util)
    formula_type = FormulaType.PT
    postorder_iterative(program.get_pt_specs(), generate_assembly_util)

    for at_instr in [a for a in program.atomics.values() if a.atid >= 0]:
        at_asm.append(at_instr)

    at_asm.sort(key=lambda n: n.atid)
    bz_asm.sort(key=lambda n: n.bzid)
    ft_asm.sort(key=lambda n: n.ftid)
    pt_asm.sort(key=lambda n: n.ptid)

    return (ft_asm, pt_asm, bz_asm, at_asm)


def compute_scq_size(node: Node) -> int:
    """
    Computes SCQ sizes for each node in 'a' and returns the sum of each SCQ size. Sets this sum to the total_scq_size value of program.

    Must be called *after* tlids have been assigned.
    """
    visited: List[int] = []
    total: int = 0

    def compute_scq_size_util(node: Node) -> None:
        nonlocal visited
        nonlocal total

        if node.ftid < 0 or isinstance(node, Program):
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

        node.scq_size = max(max_wpd-node.bpd,0)+3 # works for +3 b/c of some bug -- ask Brian
        total += node.scq_size

    postorder_iterative(node, compute_scq_size_util)
    node.total_scq_size = total

    return total


def generate_scq_assembly(program: Program) -> List[Tuple[int,int]]:
    ret: List[Tuple[int,int]] = []
    pos: int = 0

    compute_scq_size(program.get_ft_specs())

    def gen_scq_assembly_util(a: Node) -> None:
        nonlocal ret
        nonlocal pos

        if a.ftid < 0 or isinstance(a, SpecificationSet):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        ret.append((start_pos,end_pos))

    postorder_iterative(program.get_ft_specs(), gen_scq_assembly_util)
    program.scq_assembly = ret

    return ret


def compute_cpu_wcet(program: Program, latency_table: Dict[str, int], clk: int) -> int:
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


def compute_fpga_wcet(program: Program, latency_table: Dict[str, Tuple[float, float]], clk: float) -> float:
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


def parse(input: str) -> Program|None:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: C2POLexer = C2POLexer()
    parser: C2POParser = C2POParser()
    specs: Dict[FormulaType, SpecificationSet] = parser.parse(lexer.tokenize(input))

    if not parser.status:
        return None

    if not FormulaType.FT in specs:
        specs[FormulaType.FT] = SpecificationSet(0, FormulaType.FT, [])

    if not FormulaType.PT in specs:
        specs[FormulaType.PT] = SpecificationSet(0, FormulaType.PT, [])

    return Program(
        0,
        parser.signals,
        parser.defs,
        parser.structs,
        parser.atomics,
        specs[FormulaType.FT],
        specs[FormulaType.PT]
    )


def set_options(
    program: Program,
    impl_str: str, 
    int_width: int, 
    int_is_signed: bool, 
    float_width: int,
    at: bool, 
    bz: bool, 
    extops: bool
) -> bool:
    """Checks that the options are valid for the given implementation.
    
    Args:
        program: Target program for compilation
        impl_str: String representing one of the R2U2 implementation 
            (should be one of 'c', 'c++'/'cpp', or 'fpga'/'vhdl')
        movavg_size: Maximum size for moving average AT filter
        int_width: Width to set C2PO INT type to
        int_is_signed: If true sets INT type to signed
        float_width: Width to set C2PO FLOAT type to
        enable_at: If true enables Atomic Checker instructions
        enable_bz: If true enables Booleanizer instructions
    """
    status: bool = True
    
    impl: R2U2Implementation = str_to_r2u2_implementation(impl_str)
    program.implementation = impl

    set_types(impl, int_width, int_is_signed, float_width)

    if bz and at:
        logger.error(f" Only one of AT and BZ can be enabled")
        status = False
    
    if impl == R2U2Implementation.C:
        if not ((not bz and at) or (bz and not at)):
            logger.error(f" Exactly one of booleanizer or atomic checker must be enabled for C implementation.")
            status = False
    else: # impl == R2U2Implementation.CPP or impl == R2U2Implementation.VHDL
        if bz:
            logger.error(f" Booleanizer not available for hardware implementation.")
            status = False

    if impl == R2U2Implementation.CPP or impl == R2U2Implementation.VHDL:
        if extops:
            logger.error(f" Extended operators only support for C implementation.")
            status = False

    return status


def compile(
    input: str,
    signals_filename: str,
    impl: str = "c",
    int_width: int = 8,
    int_signed: bool = False,
    float_width: int = 32,
    output_filename: str = "r2u2_spec.bin",
    enable_assemble: bool = True,
    enable_cse: bool = False,
    enable_at: bool = False,
    enable_bz: bool = False,
    enable_extops: bool = False,
    enable_rewrite: bool = False,
    quiet: bool = False
) -> tuple[int,str,str,str,Program]:
    """Compile a C2PO input file, output generated R2U2 binaries and return error/success code.
    
    Args:
        input: Source code of a C2PO input file
        signals_filename: Name of a csv trace file or C2PO signals file
        impl: An R2U2 implementation to target. Should be one of 'c', 'c++', 'cpp', 'fpga', or 'vhdl'
        int_width: Width to set C2PO INT type to. Should be one of 8, 16, 32, or 64
        int_signed: If true sets INT type to signed
        float_width: Width to set C2PO FLOAT type to. Should be one of 32 or 64
        output_filename: Name of binary output file
        enable_assemble: If true outputs binary to output_filename
        enable_cse: If true enables Common Subexpression Elimination
        enable_at: If true enables Atomic Checker instructions
        enable_bz: If true enables Booleanizer instructions
        enable_extops: If true enables TL extended operators
        enable_rewrite: If true enables MLTL rewrite rule optimizations
        quiet: If true disables assembly output to stdout
    """
    log_stream.truncate(0)

    with contextlib.redirect_stderr(io.StringIO()) as stderr:

        program: Program|None = parse(input)

        if not program:
            logger.error(" Failed parsing.")
            return (ReturnCode.PARSE_ERROR.value,log_stream.getvalue(),stderr.getvalue(),'',Program(0,{},{},{},{},SpecificationSet(0, FormulaType.FT, []),SpecificationSet(0, FormulaType.FT, []))) # type: ignore

        if not set_options(program, impl, int_width, int_signed, float_width, 
                                enable_at, enable_bz, enable_extops):
            logger.error(" Invalid configuration options.")
            return (ReturnCode.INVALID_OPTIONS.value,log_stream.getvalue(),stderr.getvalue(),'',Program(0,{},{},{},{},SpecificationSet(0, FormulaType.FT, []),SpecificationSet(0, FormulaType.FT, []))) # type: ignore

        # parse csv/signals file
        program.signal_mapping = collect_signals(program)

        # type check
        if not type_check(program, enable_at, enable_bz):
            logger.error(" Failed type check.")
            return (ReturnCode.TYPE_CHECK_ERROR.value,log_stream.getvalue(),stderr.getvalue(),'',Program(0,{},{},{},{},SpecificationSet(0, FormulaType.FT, []),SpecificationSet(0, FormulaType.FT, []))) # type: ignore

        rewrite_contracts(program)
        rewrite_set_aggregation(program)
        rewrite_struct_access(program)

        if enable_rewrite:
            optimize_rewrite_rules(program)

        # rewrite without extended operators if enabled
        if not enable_extops:
            rewrite_extended_operators(program)

        # common sub-expressions elimination
        if enable_cse:
            optimize_cse(program)

        # generate alias file
        aliases = generate_aliases(program)

        # generate assembly
        (ft_asm, pt_asm, bz_asm, at_asm) = generate_assembly(program, enable_at, enable_bz)
        scq_asm: List[Tuple[int,int]] = generate_scq_assembly(program)
        program.assembly = bz_asm + ft_asm + pt_asm # type: ignore


        # print asm if 'quiet' option not enabled
        asm = ""
        if not quiet:
            if enable_at:
                asm += "AT Assembly:\n"
                for s in at_asm:
                    asm += f"\t{s.at_asm()}\n"
            if enable_bz:
                asm += "BZ Assembly:\n"
                for s in bz_asm:
                    asm += f"\t{s.bz_asm()}\n"

            asm += "FT Assembly:\n"
            for a in ft_asm:
                asm += f"\t{a.ft_asm()}\n"

            asm += "PT Assembly:\n"
            for a in pt_asm:
                asm += f"\t{a.pt_asm()}\n"

            asm += "SCQ Assembly:\n"
            for s in scq_asm:
                asm += f"\t{s}\n"

        return (ReturnCode.SUCCESS.value,log_stream.getvalue(),stderr.getvalue(),asm,program)

