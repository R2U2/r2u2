import re
from logging import getLogger

from antlr4 import CommonTokenStream, InputStream

from .ast import *
from .parser.C2POLexer import C2POLexer
from .parser.C2POParser import C2POParser
from .util import *
from .visitor import Visitor

# from .assembler import assemble

logger = getLogger(logger_name)
    

def type_check(prog: AST, bz: bool, st: StructDict) -> bool:
    status: bool = True
    explored: list[AST] = []
    context: dict[str,Type] = {}

    def type_check_util(a: AST) -> None:
        nonlocal status

        if a in explored:
            return
        explored.append(a)

        if not bz and not isinstance(a,LIT) and isinstance(a,BZ_EXPR):
            status = False
            logger.error('%d: Found BZ expression, but Booleanizer expressions disabled\n\t%s', a.ln, a)


        # enforce no mixed-time formulas
        if isinstance(a,TL_FT_OP):
            for c in a.children:
                if c.formula_type == FormulaType.PT:
                    status = False
                    logger.error('%d: Mixed-time formulas unsupported\n\t%s', a.ln, a)
            a.formula_type = FormulaType.FT
        elif isinstance(a,TL_PT_OP):
            for c in a.children:
                if c.formula_type == FormulaType.FT:
                    status = False
                    logger.error('%d: Mixed-time formulas unsupported\n\t%s', a.ln, a)
            a.formula_type = FormulaType.PT
        else:
            # not a TL op, propagate formula type from children
            for c in a.children:
                if c.formula_type == FormulaType.FT or c.formula_type == FormulaType.PT:
                    a.formula_type = c.formula_type


        if isinstance(a,SIGNAL) or isinstance(a,CONST) or isinstance(a,PROGRAM):
            pass
        elif isinstance(a,SPEC):
            child = a.get_expr()

            if not child.type == Bool():
                status = False
                logger.error(f'{a.ln}: Specification must be of boolean type (found \'{child.type}\')\n\t{a}')
        elif isinstance(a,REL_OP) or isinstance(a,ARITH_BIN_OP):
            lhs = a.get_lhs()
            rhs = a.get_rhs()

            if isinstance(lhs,INT) and rhs.type == Float():
                lhs = FLOAT(lhs.ln,lhs.val)
                a.children[0] = lhs
            elif isinstance(rhs,INT) and lhs.type == Float():
                rhs = FLOAT(rhs.ln,rhs.val)
                a.children[1] = rhs

            if lhs.type != rhs.type:
                status = False
                logger.error(f'{a.ln}: Invalid operands for \'{a.name}\', must be of same type (found \'{lhs.type}\' and \'{rhs.type}\')\n\t{a}')

            if isinstance(a,REL_OP):
                a.type = Bool()
            else:
                a.type = lhs.type
        elif isinstance(a,ARITH_UNARY_OP):
            a.type = a.get_operand().type
        elif isinstance(a,LOG_OP):
            for c in a.children:
                if c.type != Bool():
                    status = False
                    logger.error(f'{a.ln}: Invalid operands for \'{a.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{a}')

            a.type = Bool()
        elif isinstance(a,TL_OP):
            for c in a.children:
                if c.type != Bool():
                    status = False
                    logger.error(f'{a.ln}: Invalid operands for \'{a.name}\', found \'{c.type}\' (\'{c}\') but expected \'bool\'\n\t{a}')

            status = status and a.interval.lb <= a.interval.ub
            a.type = Bool()
        elif isinstance(a,SET):
            t: Type = NoType() if len(a.children) == 0 else a.children[0].type
            for m in a.children:
                if m.type != t:
                    status = False
                    logger.error(f'{a.ln}: Set \'{a}\' must be of homogeneous type (found \'{m.type}\' and \'{t}\')')

            a.type = Set(t)
        elif isinstance(a,VAR):
            if a.name in context.keys():
                a.type = context[a.name]
            else:
                status = False
                logger.error(f'{a.ln}: Variable \'{a}\' not recognized')
        elif isinstance(a,SET_AGG_OP):
            del context[a.get_boundvar().name]
            if a.get_expr().type != Bool():
                status = False
                logger.error(f'{a.ln}: Set aggregation argument must be Boolean (found \'{a.get_expr().type}\')')
            a.type = Bool()
        elif isinstance(a,STRUCT):
            a.type = Struct(a.name)
        elif isinstance(a,STRUCT_ACCESS):
            st_name = a.get_struct().type.name
            if st_name in st.keys() and a.member in st[st_name].keys():
                a.type = st[st_name][a.member]
            else:
                status = False
                logger.error(f'{a.ln}: Member \'{a.member}\' invalid for struct \'{a.get_struct().name}\'')
        else:
            logger.error(f'{a.ln}: Invalid expression\n\t{a}')
            status = False

        if isinstance(a.type,Set):
            for p in a.parents:
                if isinstance(p,SET_AGG_OP):
                    context[p.get_boundvar().name] = a.type.member_type

    postorder(prog,type_check_util)

    return status


def rewrite_ops(prog: PROGRAM) -> None:

    def rewrite_ops_util(a: AST) -> None:
        ln: int = a.ln
        
        if isinstance(a,LOG_BIN_OP):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()

            if isinstance(a,LOG_BIN_OR):
                rewrite(a,LOG_NEG(ln, LOG_BIN_AND(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs))))
            elif isinstance(a,LOG_XOR):
                rewrite(a,LOG_BIN_AND(ln, LOG_NEG(ln, LOG_BIN_AND(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs))), \
                                                LOG_NEG(ln, LOG_BIN_AND(ln, lhs, rhs))))
            elif isinstance(a,LOG_IMPL):
                rewrite(a,LOG_NEG(ln, LOG_BIN_AND(ln, lhs, LOG_NEG(ln, rhs))))
        elif isinstance(a, TL_FT_BIN_OP):
            lhs: AST = a.get_lhs()
            rhs: AST = a.get_rhs()
            bounds: Interval = a.interval

            rewrite(a, LOG_NEG(ln, TL_UNTIL(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs), bounds.lb, bounds.ub)))
        elif isinstance(a, TL_FT_UNARY_OP):
            operand: AST = a.get_operand()
            bounds: Interval = a.interval

            rewrite(a, TL_UNTIL(ln, BOOL(ln, True), operand, bounds.lb, bounds.ub))

    postorder(prog, rewrite_ops_util)


def rewrite_struct_access(prog: PROGRAM) -> None:

    def rewrite_struct_access_util(a: AST) -> None:
        if isinstance(a,STRUCT_ACCESS):
            print(a)
            s: STRUCT = a.get_struct()
            rewrite(a,s.members[a.member])

    postorder(prog, rewrite_struct_access_util)


def rewrite_set_agg(prog: PROGRAM) -> None:

    # could be done far more efficiently...currently traverses each set agg
    # expression sub tree searching for struct accesses. better approach: keep
    # track of these accesses on the frontend
    def rewrite_struct_access_util(a: AST) -> None:
        for c in a.children:
            rewrite_struct_access_util(c)

        if isinstance(a,STRUCT_ACCESS) and not isinstance(a.get_struct(),VAR):
            s: STRUCT = a.get_struct()
            rewrite(a,s.members[a.member])
    
    def rewrite_set_agg_util(a: AST) -> None:
        cur: AST = a

        if isinstance(a, FOR_EACH):
            print('a: '+str(a))
            cur = LOG_AND(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().children])
            print('cur: '+str(cur))
            set_parents(cur)
            rewrite(a, cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, FOR_SOME):
            cur = LOG_OR(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().children])
            rewrite(a, cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, FOR_EXACTLY_N):
            s: SET = a.get_set()
            cur = REL_EQ(a.ln, COUNT(a.ln, INT(a.ln, s.get_max_size()), [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().children]), INT(a.ln, a.num))
            rewrite(a, cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, FOR_AT_LEAST_N):
            s: SET = a.get_set()
            cur = REL_GTE(a.ln, COUNT(a.ln, INT(a.ln, s.get_max_size()), [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().children]), INT(a.ln, a.num))
            rewrite(a, cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, FOR_AT_MOST_N):
            s: SET = a.get_set()
            cur = REL_LTE(a.ln, COUNT(a.ln, INT(a.ln, s.get_max_size()), [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().children]), INT(a.ln, a.num))
            rewrite(a, cur)
            rewrite_struct_access_util(cur)

        for c in cur.children:
            rewrite_set_agg_util(c)

    rewrite_set_agg_util(prog)
    print(prog)


def optimize_cse(prog: PROGRAM) -> None:
    S: dict[str,AST] = {}
    
    def optimize_cse_util(a: AST) -> None:
        nonlocal S
        c: int
        i: str

        for c in range(0,len(a.children)):
            child = a.children[c]
            i = str(child)

            if i in list(S):
                a.children[c] = S[i]
            else:
                S[i] = a.children[c]
            
    postorder(prog,optimize_cse_util)


def gen_alias(prog: PROGRAM) -> str:
    s: str = ''

    for num,spec in prog.specs.items():
        if spec.name in [c.name for c in prog.contracts.values()]: 
            # then formula is part of contract, ignore
            continue
        s += 'F ' + spec.name + ' ' + str(num) + '\n'

    for num,contract in prog.contracts.items():
        s += 'C ' + contract.name + ' ' + str(num) + ' ' + \
            str(num+1) + ' ' + str(num+2) + '\n'

    return s


def compute_scq_size(prog: PROGRAM) -> None:

    def compute_scq_size_util(a: AST) -> None:
        if not isinstance(a, TL_EXPR) or isinstance(a, PROGRAM):
            return

        if isinstance(a, SPEC):
            a.scq_size = 1
            return

        siblings: list[AST] = []
        for p in a.parents:
            for s in p.children:
                if not s == a:
                    siblings.append(s)

        wpd: int = max([s.wpd for s in siblings]+[0])

        a.scq_size = max(wpd-a.bpd,0)+1 # works for +3 b/c of some bug -- ask Brian

    postorder(prog,compute_scq_size_util)


def total_scq_size(prog: PROGRAM) -> int:
    mem: int = 0

    def total_scq_size_util(a: AST) -> None:
        nonlocal mem
        mem += a.scq_size
        # if isinstance(a,TL_EXPR) and not isinstance(a, PROGRAM):
        #     print('mem('+str(a)+') = '+str(a.scq_size))
    postorder(prog,total_scq_size_util)
    return mem


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
            for id in lines[0].split(','):
                mapping[id] = cnt
                cnt += 1
    else: # TODO, implement signal mapping file format
        return {}

    return mapping
    

def assign_ids(prog: PROGRAM, signal_mapping: dict[str,int]) -> None:
    tlid: int = 0
    bzid: int = 0
    atid: int = 0

    def assign_ids_util(a: AST) -> None:
        nonlocal signal_mapping
        nonlocal tlid
        nonlocal bzid
        nonlocal atid

        if isinstance(a,BOOL) or a.tlid > -1:
            return

        if isinstance(a,TL_EXPR):
            a.tlid = tlid
            tlid += 1

        if isinstance(a,BZ_EXPR):
            
            for p in a.parents:
                if isinstance(p,TL_EXPR):
                    a.atid = atid
                    atid += 1
                    a.tlid = tlid
                    tlid += 1

        if isinstance(a,SIGNAL):
            if not a.name in signal_mapping.keys():
                logger.error(f'{a.ln}: Signal \'{a}\' not referenced in signal mapping')
            else:
                a.sid = signal_mapping[a.name]

    postorder(prog,assign_ids_util)


def gen_bz_assembly(prog: PROGRAM) -> str:
    bz_visited: list[AST] = []
    bzasm: str = ''

    def gen_bzasm_util_pre(a: AST) -> None:
        # load next element's data into registers
        pass

    def gen_bzasm_util_post(a: AST) -> None:
        nonlocal bzasm
        nonlocal bz_visited

        if isinstance(a,BZ_EXPR):
            if not a in bz_visited:
                bzasm += a.bzasm()
                bz_visited.append(a)

                for p in a.parents:
                    if isinstance(p,TL_EXPR):
                        bzasm += a.bzasm_store()
                        break
                    
                # for i in range(0,len(a.parents)-1): # type: ignore
                #     bzasm += a.bzasm_dup()

    traverse(prog,gen_bzasm_util_pre,gen_bzasm_util_post)

    return bzasm[:-1] # remove dangling '\n'


def gen_tl_assembly(prog: PROGRAM) -> str:
    tl_visited: list[int] = []
    tlasm: str = ''

    def gen_tlasm_util(a: AST) -> None:
        nonlocal tlasm
        nonlocal tl_visited

        if isinstance(a,TL_EXPR):
            if not a.tlid in tl_visited:
                tlasm += a.tlasm()
                tl_visited.append(a.tlid)
        
        if isinstance(a,BZ_EXPR) and a.atid > -1:
            if not a.tlid in tl_visited:
                tlasm += a.tlasm()
                tl_visited.append(a.tlid)

    postorder(prog,gen_tlasm_util)
    
    return tlasm


def gen_scq_assembly(prog: PROGRAM) -> str:
    s: str = ''
    pos: int = 0

    compute_scq_size(prog)
    # print(total_scq_size(prog))

    def gen_scq_assembly_util(a: AST) -> None:
        nonlocal s
        nonlocal pos

        if isinstance(a,PROGRAM) or isinstance(a,BZ_EXPR):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        s += str(start_pos) + ' ' + str(end_pos) + '\n'

    postorder(prog,gen_scq_assembly_util)
    return s


def gen_assembly(prog: PROGRAM, signal_mapping: dict[str,int]) -> list[str]:
    assign_ids(prog,signal_mapping)
    
    bzasm: str = gen_bz_assembly(prog)
    tlasm: str = gen_tl_assembly(prog)
    scq_asm: str = gen_scq_assembly(prog)

    return [bzasm,tlasm,'n0: endsequence',scq_asm]


def parse(input: str) -> list[PROGRAM]:
    lexer: C2POLexer = C2POLexer(InputStream(input))
    stream: CommonTokenStream = CommonTokenStream(lexer)
    parser: C2POParser = C2POParser(stream)
    parse_tree = parser.start()
    # print(parse_tree.toStringTree(recog=parser))
    v: Visitor = Visitor()
    progs: list[PROGRAM] = v.visitStart(parse_tree) # type: ignore
    if v.status:
        return progs
    else:
        return []


def compile(input: str, sigs: str, output_path: str, bz: bool, extops: bool, quiet: bool) -> None:
    # parse input, progs is a list of configurations (each SPEC block is a configuration)
    progs: list[PROGRAM] = parse(input)

    if len(progs) < 1:
        logger.error(' Failed parsing.')
        return

    set_parents(progs[0])

    # type check
    if not type_check(progs[0],bz,progs[0].structs):
        logger.error(' Failed type check')
        return

    rewrite_set_agg(progs[0])
    rewrite_struct_access(progs[0])

    # rewrite without extended operators if enabled
    if not extops:
        rewrite_ops(progs[0])

    # common sub-expressions elimination
    optimize_cse(progs[0])

    # generate alias file
    alias = gen_alias(progs[0])

    # parse csv/signals file
    signal_mapping: dict[str,int] = parse_signals(sigs)

    # generate assembly
    bzasm,ftasm,ptasm,ftscqasm = gen_assembly(progs[0],signal_mapping)

    # print asm if 'quiet' option not enabled
    # uses re.sub to get nice tabs
    if not quiet:
        if bz:
            logger.info(Color.HEADER+' BZ Assembly'+Color.ENDC+':\n'+ \
                re.sub('\n','\n\t',re.sub('^','\t',bzasm)))
        logger.info(Color.HEADER+' FT Assembly'+Color.ENDC+':\n'+ \
            re.sub('\n','\n\t',re.sub('^','\t',ftasm)))
        logger.info(Color.HEADER+' PT Assembly'+Color.ENDC+':\n'+ \
            re.sub('\n','\n\t',re.sub('^','\t',ptasm)))

    # write assembly and assemble all files into binaries
    with open(output_path+'alias.txt','w') as f:
        f.write(alias)

    if bz:
        with open(output_path+'bz.asm','w') as f:
            f.write(bzasm)

    with open(output_path+'ft.asm','w') as f:
        f.write(ftasm)

    with open(output_path+'pt.asm','w') as f:
        f.write(ptasm)

    with open(output_path+'ftscq.asm','w') as f:
        f.write(ftscqasm)

    # assemble(output_path+'r2u2.bin', bzasm, ftasm, ptasm, ftscqasm)



    

    