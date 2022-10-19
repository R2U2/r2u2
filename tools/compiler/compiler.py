import re
from logging import getLogger
from typing import cast, Callable, Any
from antlr4 import InputStream, CommonTokenStream # type: ignore

from .ast import *
from .parser.C2POLexer import C2POLexer
from .parser.C2POParser import C2POParser
from .visitor import Visitor
from .util import *
# from .assembler import assemble

logger = getLogger(logger_name)

def postorder(a: AST, func: Callable[[AST],Any]) -> None:
    c: AST
    for c in a.children:
        postorder(c,func)
    func(a)


def preorder(a: AST, func: Callable[[AST],Any]) -> None:
    func(a)
    c: AST
    for c in a.children:
        preorder(c,func)

    
def type_check(prog: AST, bz: bool) -> bool:
    status: bool = True

    def type_check_util(a: AST) -> None:
        nonlocal bz
        nonlocal status
        c: AST

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


        if isinstance(a,ATOM) or isinstance(a,VAR) or isinstance(a,CONST) or isinstance(a,PROGRAM):
            pass
        elif isinstance(a,SPEC):
            child = cast(EXPR,a.children[0])

            if not child.type == Type.BOOL:
                status = False
                logger.error('%d: Specification must be of boolean type (found \'%s\')\n\t%s', 
                        a.ln, to_str(child.type), a)
        elif isinstance(a,REL_OP) or isinstance(a,ARITH_OP):
            lhs = a.children[0]
            rhs = a.children[1]

            if isinstance(lhs,INT) and rhs.type == Type.FLOAT:
                lhs = FLOAT(lhs.ln,lhs.val)
                a.children[0] = lhs
            elif isinstance(rhs,INT) and lhs.type == Type.FLOAT:
                rhs = FLOAT(rhs.ln,rhs.val)
                a.children[1] = rhs

            if lhs.type != rhs.type:
                status = False
                logger.error('%d: Invalid operands for %s, must be of same type (found \'%s\' and \'%s\')\n\t%s', 
                        a.ln, a.name, to_str(lhs.type), to_str(rhs.type), a)

            if isinstance(a,REL_OP):
                a.type = Type.BOOL
            else:
                a.type = lhs.type
        elif isinstance(a,LOG_OP):
            for c in a.children:
                if c.type != Type.BOOL:
                    status = False
                    logger.error('%d: Invalid operands for %s, found \'%s\' (\'%s\') but expected \'bool\'\n\t%s', 
                            a.ln, a.name, to_str(c.type), c, a)

            a.type = Type.BOOL
        elif isinstance(a,TL_OP):
            for c in a.children:
                if c.type != Type.BOOL:
                    status = False
                    logger.error('%d: Invalid operands for %s, found \'%s\' (\'%s\') but expected \'bool\'\n\t%s', 
                            a.ln, a.name, to_str(c.type), c, a)

            status = status and a.interval.lb <= a.interval.ub
            a.type = Type.BOOL
        else:
            logger.error('%d: Invalid expression\n\t%s', a.ln, a)
            status = False

    postorder(prog,type_check_util)
    return status


def rewrite_ops(prog: PROGRAM) -> None:

    def rewrite_ops_util(a: AST) -> None:
        ln: int = a.ln

        for c in range(0,len(a.children)):
            cur = a.children[c]

            if isinstance(cur,LOG_BIN_OP):
                lhs: AST = cur.children[0]
                rhs: AST = cur.children[1]
            
                if isinstance(cur,LOG_OR):
                    a.children[c] = LOG_NEG(ln, LOG_AND(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs)))
                elif isinstance(cur,LOG_XOR):
                    a.children[c] = LOG_AND(ln, LOG_NEG(ln, LOG_AND(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs))), \
                                                LOG_NEG(ln, LOG_AND(ln, lhs, rhs)))
                elif isinstance(cur,LOG_IMPL):
                    a.children[c] = LOG_NEG(ln, LOG_AND(ln, lhs, LOG_NEG(ln, rhs)))
            elif isinstance(cur, TL_FT_BIN_OP):
                lhs: AST = cur.children[0]
                rhs: AST = cur.children[1]
                bounds: Interval = cur.interval

                a.children[c] = LOG_NEG(ln, TL_UNTIL(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs), bounds.lb, bounds.ub))
            elif isinstance(cur, TL_FT_UNARY_OP):
                operand: AST = cur.children[0]
                bounds: Interval = cur.interval

                a.children[c] = TL_UNTIL(ln, BOOL(ln, True), operand, bounds.lb, bounds.ub)

    postorder(prog, rewrite_ops_util)


def optimize_cse(prog: PROGRAM) -> None:
    S: dict[str,AST] = {}
    
    def optimize_cse(a: AST) -> None:
        nonlocal S
        c: int
        i: str

        if isinstance(a,ATOM):
            return

        for c in range(0,len(a.children)):
            child = a.children[c]
            i = str(child)

            if i in list(S):
                a.children[c] = S[i]
            else:
                S[i] = a.children[c]
            
    postorder(prog,optimize_cse)


def insert_atomics(prog: PROGRAM) -> None:
    bzidx: int = 0

    def insert_atom(a: AST) -> None:
        nonlocal bzidx
        
        for c in range(0,len(a.children)):
            child = a.children[c]
            if isinstance(a,TL_EXPR) and isinstance(child,BZ_EXPR) and not isinstance(child,BOOL) \
                    and not isinstance(a,ATOM) and not isinstance(child,ATOM):
                new: ATOM = ATOM(a.ln,child,bzidx)
                a.children[c] = new

    postorder(prog,insert_atom)


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

    # for set_name, atomics in self.def_sets.items():
    #     atoms = [str(self.atomics.get(atom, atom[1:])) for atom in atomics[1]]
    #     s += 'R ' + set_name + ' ' + str(atomics[0]) + ' ' + ' '.join(atoms) + '\n'

    return s


def compute_scq_size(prog: PROGRAM) -> None:
    
    def compute_scq_size_util(a: AST) -> None:
        if isinstance(a, PROGRAM):
            # all SPEC scq_size = 1
            for c in a.children:
                c.scq_size = 1
            return

        wpd: int = 0
        for c in a.children:
            if c.wpd > wpd:
                wpd = c.wpd

        for c in a.children:
            c.scq_size = max(wpd-c.bpd,0)+3 # +3 b/c of some bug -- ask Brian

    preorder(prog,compute_scq_size_util)


def assign_ids(prog: PROGRAM) -> None:
    order: dict[str,int] = prog.order
    tlid: int = 0
    bzid: int = 0
    atid: int = 0

    def assign_ids_util(a: AST) -> None:
        nonlocal order
        nonlocal tlid
        nonlocal bzid
        nonlocal atid

        if isinstance(a,BOOL) or a.tlid > -1 or a.bzid > -1:
            return

        if isinstance(a,BZ_EXPR):
            a.bzid = bzid
            bzid += 1

        if isinstance(a,TL_EXPR):
            a.tlid = tlid
            tlid += 1

        if isinstance(a,ATOM):
            a.atid = atid
            atid += 1

        if isinstance(a,VAR):
            a.sid = order[a.name]

    postorder(prog,assign_ids_util)


def gen_bz_assembly(prog: PROGRAM) -> str:
    bz_visited: list[int] = []
    bzasm: str = ''

    def gen_bzasm_util(a: AST) -> None:
        nonlocal bzasm
        nonlocal bz_visited

        if not isinstance(a,ATOM) and isinstance(a,TL_EXPR):
            return

        if not a.bzid in bz_visited:
            bzasm += a.bzasm()
            bz_visited.append(a.bzid)

    postorder(prog,gen_bzasm_util)

    return bzasm[:-1] # remove dangling '\n'


def gen_tl_assembly(prog: PROGRAM) -> str:
    tl_visited: list[int] = []
    tlasm: str = ''

    def gen_tlasm_util(a: AST) -> None:
        nonlocal tlasm
        nonlocal tl_visited

        if not isinstance(a,ATOM) and isinstance(a,BZ_EXPR):
            return

        if not a.tlid in tl_visited:
            tlasm += a.tlasm()
            tl_visited.append(a.tlid)

    postorder(prog,gen_tlasm_util)
    
    return tlasm


def gen_scq_assembly(prog: PROGRAM) -> str:
    s: str = ''
    pos: int = 0

    compute_scq_size(prog)

    def gen_scq_assembly_util(a: AST) -> None:
        nonlocal s
        nonlocal pos

        if isinstance(a,PROGRAM) or isinstance(a,CONST):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        s += str(start_pos) + ' ' + str(end_pos) + '\n'

    postorder(prog,gen_scq_assembly_util)
    return s


def gen_assembly(prog: PROGRAM) -> list[str]:
    assign_ids(prog)
    
    bzasm: str = gen_bz_assembly(prog)
    tlasm: str = gen_tl_assembly(prog)
    scq_asm: str = gen_scq_assembly(prog)

    return [bzasm,tlasm,'n0: end sequence',scq_asm]


def parse(input: str) -> list[PROGRAM]:
    lexer: C2POLexer = C2POLexer(InputStream(input))
    stream: CommonTokenStream = CommonTokenStream(lexer)
    parser: C2POParser = C2POParser(stream)
    parse_tree = parser.start()
    # print(parse_tree.toStringTree(recog=parser))
    v: Visitor = Visitor()
    return v.visitStart(parse_tree)


def compile(input: str, output_path: str, bz: bool, extops: bool, quiet: bool) -> None:
    # parse input, progs is a list of configurations (each SPEC block is a configuration)
    progs: list[PROGRAM] = parse(input)

    if len(progs) < 1:
        return

    # type check
    if not type_check(progs[0],bz):
        logger.error('Failed type check')
        return

    # rewrite without extended operators if enabled
    if not extops:
        rewrite_ops(progs[0])

    # demarcate TL and BZ nodes with ATOM nodes
    insert_atomics(progs[0])

    # common sub-expressions elimination
    optimize_cse(progs[0])

    # generate alias file
    alias = gen_alias(progs[0])

    # generate assembly
    bzasm,ftasm,ptasm,ftscqasm = gen_assembly(progs[0])

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
