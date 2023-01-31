from argparse import PARSER
import re
from logging import getLogger

from .ast import *
from .parser import C2POLexer
from .parser import C2POParser
from .logger import *

# from .assembler import assemble

logger = getLogger(COLOR_LOGGER_NAME)

SUCCESS_CODE: int = 0
PARSER_ERROR_CODE: int = 1
TYPE_CHECK_ERROR_CODE: int = 2

# class C2PO:
#     """Configuration Compiler for Property Organization"""

#     def __init__(self, mltl_filename: str, signal_filename: str, output_path: str, booleanizer: bool, \
#             extended_operators: bool, quiet: bool) -> None:
#         pass


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

        if not bz and isinstance(a,BZExpr) and not isinstance(a,Signal) and not isinstance(a,Bool):
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

            status = status and a.interval.lb <= a.interval.ub
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


def gen_alias(program: Program) -> str:
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


def compute_scq_size(program: Program) -> None:
    visited: list[AST] = []

    def compute_scq_size_util(a: AST) -> None:
        if not isinstance(a, TLExpr) or isinstance(a, Program):
            return

        if a in visited:
            return
        visited.append(a)

        if isinstance(a, Specification):
            a.scq_size = 1
            return

        siblings: list[AST] = []
        for p in a.get_parents():
            for s in p.get_children():
                if not s == a:
                    siblings.append(s)

        wpd: int = max([s.wpd for s in siblings]+[1])

        a.scq_size = max(wpd-a.bpd,0)+1 # works for +3 b/c of some bug -- ask Brian
 
    postorder(program,compute_scq_size_util)


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
            for id in [s.strip() for s in lines[0].split(',')]:
                mapping[id] = cnt
                cnt += 1
    else: # TODO, implement signal mapping file format
        return {}

    return mapping
    

def assign_ids(program: Program, signal_mapping: dict[str,int]) -> None:
    tlid: int = 0
    bzid: int = 0
    atid: int = 0

    cur_sid: int = 0
    signals: dict[AST,int] = {}

    def assign_ids_util(a: AST) -> None:
        nonlocal signal_mapping
        nonlocal tlid
        nonlocal bzid
        nonlocal atid
        nonlocal cur_sid
        nonlocal signals

        if isinstance(a,Bool) or a.tlid > -1 or a.bzid > -1:
            return

        if isinstance(a,TLExpr):
            a.tlid = tlid
            tlid += 1

        if isinstance(a,BZExpr):
            for p in a.get_parents():
                if isinstance(p,TLExpr):
                    a.atid = atid
                    atid += 1
                    a.tlid = tlid
                    tlid += 1
                    break

        if isinstance(a,Signal):
            if a in signals.keys():
                a.sid = signals[a]
            else:
                a.sid = cur_sid
                cur_sid += 1
            
            for p in a.get_parents():
                if isinstance(p,TLExpr):
                    a.tlid = tlid
                    tlid += 1
                    break
                    
    postorder(program,assign_ids_util)


def generate_assembly(program: Program, signal_mapping: dict[str,int]) -> list[AST]:
    visited: set[AST] = set()
    available_registers: set[int] = set()
    max_register: int = 0
    asm: list[AST] = []

    # logger.info(program)

    def generate_assembly_util(a: AST) -> None:
        nonlocal visited
        nonlocal available_registers
        nonlocal max_register
        nonlocal asm

        # Visit each TL node exactly once
        # Visit BZ literals as many times as necessary
        # Visit all other BZ nodes once, store and load using registers

        if isinstance(a,TLExpr):
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

        elif isinstance(a,BZExpr):
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
    
    return asm


def generate_scq_assembly(program: Program) -> list[tuple[int,int]]:
    ret: list[tuple[int,int]] = []
    pos: int = 0

    compute_scq_size(program)

    def gen_scq_assembly_util(a: AST) -> None:
        nonlocal ret
        nonlocal pos

        if isinstance(a,Program) or not isinstance(a,TLExpr):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        ret.append((start_pos,end_pos))

    postorder(program,gen_scq_assembly_util)
    return ret


def validate_booleanizer_stack(asm: list[AST]) -> bool:
    return True


def parse(input: str) -> list[Program]:
    lexer: C2POLexer = C2POLexer()
    parser: C2POParser = C2POParser()
    return parser.parse(lexer.tokenize(input))


def compile(input: str, sigs: str, output_path: str, bz: bool, extops: bool, color: bool, quiet: bool) -> tuple[int,AST,list[AST],str,int]:
    # parse input, programs is a list of configurations (each SPEC block is a configuration)
    programs: list[Program] = parse(input)

    if len(programs) < 1:
        logger.error(' Failed parsing.')
        return (PARSER_ERROR_CODE,AST(0,[]),[],'',0)

    # type check
    if not type_check(programs[0],bz,programs[0].structs):
        logger.error(' Failed type check')
        return (TYPE_CHECK_ERROR_CODE,AST(0,[]),[],'',0)

    rewrite_set_aggregation(programs[0])
    rewrite_struct_access(programs[0])

    # rewrite without extended operators if enabled
    if not extops:
        rewrite_extended_operators(programs[0])

    # common sub-expressions elimination
    optimize_cse(programs[0])

    # generate alias file
    # alias = gen_alias(programs[0])

    # parse csv/signals file
    signal_mapping: dict[str,int] = parse_signals(sigs)

    # generate assembly
    asm: list[AST] = generate_assembly(programs[0],signal_mapping)
    scq_asm: list[tuple[int,int]] = generate_scq_assembly(programs[0])

    # print asm if 'quiet' option not enabled
    asm_str: str = ''
    if not quiet:
        print(Color.HEADER+' Generated Assembly'+Color.ENDC+':')

    for a in asm:
        asm_str += '\t'+a.asm()
        if not quiet:
            print('\t'+a.asm())

    if not quiet:
        print(Color.HEADER+' Generated SCQs'+Color.ENDC+':')

    for s in scq_asm:
        asm_str += '\t'+str(s)
        if not quiet:
            print('\t'+str(s))

    postorder_ast: list[AST] = []
    def post_sort(a: AST) ->  None:
        nonlocal postorder_ast
        postorder_ast.append(a)
    postorder(programs[0],post_sort)

    return (SUCCESS_CODE,programs[0],postorder_ast,asm_str,sum([a.scq_size for a in asm]))
