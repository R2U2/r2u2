import os
import re
from logging import getLogger
from typing import cast, Callable, Any
from antlr4 import InputStream, CommonTokenStream # type: ignore

from .ast import *
from .parser.C2POLexer import C2POLexer
from .parser.C2POParser import C2POParser
from .visitor import Visitor
from .util import *

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

            if not child._type == Type.BOOL:
                status = False
                logger.error('%d: Specification must be of boolean type (found \'%s\')\n\t%s', a.ln, to_str(child._type), a)
        elif isinstance(a,REL_OP) or isinstance(a,ARITH_OP):
            lhs = a.children[0]
            rhs = a.children[1]

            if lhs._type != rhs._type:
                status = False
                logger.error('%d: Invalid operands for %s, must be of same type (found \'%s\' and \'%s\')\n\t%s', a.ln, a.name, to_str(lhs._type), to_str(rhs._type), a)

            if isinstance(a,REL_OP):
                a._type = Type.BOOL
            else:
                a._type = lhs._type
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

    for spec,num in prog.specs.items():
        s += 'F ' + spec.name + ' ' + str(num) + '\n'

    # for contract, formula_num in self.contracts.items():
    #     s += 'C ' + contract + ' ' + str(formula_num) + ' ' + \
    #         str(formula_num+1) + ' ' + str(formula_num+2) + '\n'
    # for signal, index in self.signals.items():
    #     s += 'S ' + signal + ' ' + str(index) + '\n'
    # for atom, index in self.atomics.items():
    #     s += 'A ' + atom + ' ' + str(index) + '\n'
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
    nid: int = 0
    bid: int = 0
    bzidx: int = 0

    def assign_ids_util(a: AST) -> None:
        nonlocal order
        nonlocal nid
        nonlocal bid
        nonlocal bzidx

        if isinstance(a,BOOL) or a.nid > -1 or a.bid > -1:
            return
        elif isinstance(a,BZ_EXPR):
            a.bid = bid
            a.id = 'b'+str(bid)
            bid += 1
        else:
            a.nid = nid
            a.id = 'n'+str(nid)
            nid += 1

        if isinstance(a,ATOM):
            # print(a)
            a.bzidx = bzidx
            bzidx += 1

        if isinstance(a,VAR):
            a.sid = order[a.name]

    postorder(prog,assign_ids_util)


def gen_bz_assembly(prog: PROGRAM) -> str:
    bz_visited: list[int] = []
    bz_asm: str = ''

    def gen_bz_asm_util(a: AST) -> None:
        nonlocal bz_asm
        nonlocal bz_visited

        if not isinstance(a,ATOM) and isinstance(a,TL_EXPR):
            return

        if not a.bid in bz_visited:
            # print(a)
            bz_asm += a.bz_asm()
            bz_visited.append(a.bid)

    postorder(prog,gen_bz_asm_util)
    bz_asm += 'end'

    return bz_asm


def gen_tl_assembly(prog: PROGRAM) -> list[str]:
    tl_visited: list[int] = []
    tl_asm: str = ''

    def gen_tl_asm_util(a: AST) -> None:
        nonlocal tl_asm
        nonlocal tl_visited

        if isinstance(a,BZ_EXPR):
            return

        if not a.nid in tl_visited:
            tl_asm += a.tl_asm()
            tl_visited.append(a.nid)

    postorder(prog,gen_tl_asm_util)
    
    return tl_asm


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
    
    bz_asm: str = gen_bz_assembly(prog)
    tl_asm: str = gen_tl_assembly(prog)
    scq_asm: str = gen_scq_assembly(prog)

    return [bz_asm,tl_asm,'n0: end sequence',scq_asm]


def parse(input) -> list[PROGRAM]:
    lexer: C2POLexer = C2POLexer(InputStream(input))
    stream: CommonTokenStream = CommonTokenStream(lexer)
    parser: C2POParser = C2POParser(stream)
    parse_tree = parser.start()
    # print(parse_tree.toStringTree(recog=parser))
    v: Visitor = Visitor()
    return v.visitStart(parse_tree)


def compile(input: str, output_path: str, extops: bool, quiet: bool) -> None:
    # parse input, progs is a list of configurations (each SPEC block is a configuration)
    progs: list[PROGRAM] = parse(input)

    # type check
    if not type_check(progs[0]):
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
    bz_asm,ft_asm,pt_asm,ftscq_asm = gen_assembly(progs[0])

    # print asm if 'quiet' option not enabled
    # uses re.sub to get nice tabs
    if not quiet:
        logger.info(Color.HEADER+' BZ Assembly'+Color.ENDC+':\n'+ \
            re.sub('\n','\n\t',re.sub('^','\t',bz_asm)))
        logger.info(Color.HEADER+' FT Assembly'+Color.ENDC+':\n'+ \
            re.sub('\n','\n\t',re.sub('^','\t',ft_asm)))
        logger.info(Color.HEADER+' PT Assembly'+Color.ENDC+':\n'+ \
            re.sub('\n','\n\t',re.sub('^','\t',pt_asm)))

    # write assembly and assemble all files into binaries
    with open(output_path+'alias.txt','w') as f:
        f.write(alias)

    with open(output_path+'bz.asm','w') as f:
        f.write(bz_asm)
        # assemble_at(output_path+'at.asm',output_path,'False')

    with open(output_path+'ft.asm','w') as f:
        f.write(ft_asm)
        # assemble_ft(output_path+'ft.asm',output_path+'ftscq.asm','4',output_path,'False')

    with open(output_path+'pt.asm','w') as f:
        f.write(pt_asm)
        # assemble_pt(output_path+'pt.asm','4',output_path,'False')

    with open(output_path+'ftscq.asm','w') as f:
        f.write(ftscq_asm)

