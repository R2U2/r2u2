import os
import re
from logging import getLogger
from antlr4 import InputStream, CommonTokenStream

from .ast import *
from .parser.C2POLexer import C2POLexer
from .parser.C2POParser import C2POParser
from .visitor import Visitor
from .assembler.atas import assemble_at
from .assembler.ftas import assemble_ft
from .assembler.ptas import assemble_pt
from .util import *

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'

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


def assign_ids(prog: PROGRAM) -> None:
    order: dict[str,int] = prog.order
    nid: int = 0
    aid: int = 0

    def assign_ids_rec(a: AST, atomic: bool) -> None:
        nonlocal order
        nonlocal nid
        nonlocal aid

        if isinstance(a,CONST):
            a.id = a.name
            return
        elif isinstance(a,VAR): 
            if a.name in list(order):
                a.sid = order[a.name]
            else:
                logger.error('%d: Signal \'%s\' referenced but not defined in Order', a.name)

            a.aid = aid
            a.id = 'a'+str(aid)
            aid += 1

            if not atomic:
                a.nid = nid
                a.id = 'a'+str(nid)
                nid += 1
            return

        if isinstance(a,REL_OP) or isinstance(a,ARITH_OP) or isinstance(a,LOG_OP):
            a.aid = aid
            a.id = 'a'+str(aid)
            aid += 1

            if not atomic:
                a.nid = nid
                a.id = 'a'+str(nid)
                nid += 1

            for c in a.children:
                assign_ids_rec(c,True)
            return
        else:
            a.nid = nid
            a.id = 'a'+str(nid)
            nid += 1

            for c in a.children:
                assign_ids_rec(c,atomic)
            return

    assign_ids_rec(prog,False)


def type_check(prog: AST) -> bool:
    status: bool = True

    def type_check_util(a: AST) -> None:
        nonlocal status
        c: AST

        # enforce no mixed-time formulas
        if isinstance(a,TL_FT_OP):
            for c in a.children:
                if c.formula_type == FormulaType.PT:
                    status = False
                    logger.error('%d: Mixed-time (sub)formula detected\n\t%s', a.ln, a)
            a.formula_type = FormulaType.FT
        elif isinstance(a,TL_PT_OP):
            for c in a.children:
                if c.formula_type == FormulaType.FT:
                    status = False
                    logger.error('%d: Mixed-time (sub)formula detected\n\t%s', a.ln, a)
            a.formula_type = FormulaType.PT
        else:
            # not a TL op, propagate formula type from children
            for c in a.children:
                if c.formula_type == FormulaType.FT or c.formula_type == FormulaType.PT:
                    a.formula_type = c.formula_type


        if isinstance(a,CONST) or isinstance(a,PROGRAM):
            pass
        elif isinstance(a,SPEC):
            child = cast(EXPR,a.children[0])

            if not child._type == Type.BOOL:
                status = False
                logger.error('%d: Specification must be of boolean type (found \'%s\')\n\t%s', a.ln, to_str(child._type), a)
        elif isinstance(a,REL_OP) or isinstance(a,ARITH_OP) or isinstance(a,LOG_OP):
            lhs = a.children[0]
            rhs = a.children[1]

            if lhs._type != rhs._type:
                status = False
                logger.error('%d: Invalid operands for %s, must be of same type (found \'%s\' and \'%s\')\n\t%s', a.ln, a.name, to_str(lhs._type), to_str(rhs._type), a)

            a._type = Type.BOOL
        elif isinstance(a,LOG_OP):
            for c in a.children:
                if c._type != Type.BOOL:
                    status = False
                    logger.error('%d: Invalid operands for %s, found \'%s\' (\'%s\') but expected \'bool\'\n\t%s', a.ln, a.name, to_str(c._type), c, a)

            a._type = Type.BOOL
        elif isinstance(a,TL_OP):
            for c in a.children:
                if c._type != Type.BOOL:
                    status = False
                    logger.error('%d: Invalid operands for %s, found \'%s\' (\'%s\') but expected \'bool\'\n\t%s', a.ln, a.name, to_str(c._type), c, a)

            status = status and a.interval.lb <= a.interval.ub
            a._type = Type.BOOL
        else:
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
        for c in range(0,len(a.children)):
            child = a.children[c]
            i = str(child)

            if i in list(S):
                a.children[c] = S[i]
            else:
                S[i] = a.children[c]
            
    postorder(prog,optimize_cse)


def gen_atomic_asm(prog: PROGRAM) -> str:
    s: str = ''
    visited: dict[int,AST] = {}

    def gen_atomic_asm_util(a: AST) -> None:
        nonlocal s
        nonlocal visited

        c: int
        for c in range(0,len(a.children)):
            child = a.children[c]
            i = id(child)

    preorder(prog,gen_atomic_asm_util)
    return s[:-1] # remove final newline


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
    visited: list[int] = []
    ft_asm: str = ''

    assign_ids(prog)

    atomic_asm: str = gen_atomic_asm(prog)


    def gen_tl_assembly_util(a: AST) -> None:
        nonlocal ft_asm
        nonlocal visited

        if isinstance(a,CONST):
            return

        if not a.nid in visited:
            ft_asm += a.tl_asm()
            visited.append(a.nid)

    postorder(prog,gen_tl_assembly_util)
    
    scq_asm = gen_scq_assembly(prog)

    return [atomic_asm,ft_asm,'n0: end sequence',scq_asm]


def parse(input) -> list[PROGRAM]:
    lexer = C2POLexer(InputStream(input))
    stream = CommonTokenStream(lexer)
    parser = C2POParser(stream)
    parse_tree = parser.start()
    print(parse_tree.toStringTree(recog=parser))
    v = Visitor()
    return v.visit(parse_tree)


def compile(input: str, output_path: str, extops: bool, quiet: bool) -> None:
    # parse input, progs is a list of configurations (each SPEC block is a configuration)
    progs: list[PROGRAM] = parse(input)

    return

    # type check
    if not type_check(progs[0]):
        logger.error(' Failed type check')
        return

    # rewrite without extended operators if enabled
    if not extops:
        rewrite_ops(progs[0])

    # common sub-expressions elimination
    optimize_cse(progs[0])

    # generate assembly
    at_asm,ft_asm,pt_asm,ftscq_asm = gen_assembly(progs[0])

    # print asm if 'quiet' option not enabled
    # uses re.sub to get nice tabs
    if not quiet:
        logger.info(Color.HEADER+' AT Assembly'+Color.ENDC+':\n'+ \
                re.sub('\n','\n\t',re.sub('^','\t',at_asm)))
        logger.info(Color.HEADER+' FT Assembly'+Color.ENDC+':\n'+ \
            re.sub('\n','\n\t',re.sub('^','\t',ft_asm)))
        logger.info(Color.HEADER+' PT Assembly'+Color.ENDC+':\n'+ \
            re.sub('\n','\n\t',re.sub('^','\t',pt_asm)))

    # write assembly and assemble all files into binaries
    with open(output_path+'at.asm','w') as f:
        f.write(at_asm)
        assemble_at(output_path+'at.asm',output_path,'False')
    with open(output_path+'ft.asm','w') as f:
        f.write(ft_asm)
        assemble_ft(output_path+'ft.asm',output_path+'ftscq.asm','4',output_path,'False')
    with open(output_path+'pt.asm','w') as f:
        f.write(pt_asm)
        assemble_pt(output_path+'pt.asm','4',output_path,'False')
    with open(output_path+'ftscq.asm','w') as f:
        f.write(ftscq_asm)

