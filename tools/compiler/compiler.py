## Description: 1. optimize the AST; 2. assign SCQ size; 3. generate assembly
## Author: Chris Johannsen
import os

from antlr4 import InputStream, CommonTokenStream

from .ast import *
from .parser.C2POLexer import C2POLexer
from .parser.C2POParser import C2POParser
from .visitor import Visitor
from .assembler.atas import assemble_at
from .assembler.ftas import assemble_ft
from .assembler.ptas import assemble_pt

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'


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

### TODO Question:
### only reference to subformulas appears supported in the c version
### -- why not only support this? do we forsee supporting direct
### atomic/immediate loads?
def assign_nid(a: AST) -> None:
    n = 0

    def assign_nid_util(a: AST) -> None:
        nonlocal n

        # if a is const, skip
        if isinstance(a,CONST):
            a.id = a.name[0]
            return
        
        # assign nid to nodes we have not seen
        # by default, nid = -1
        if a.nid < 0:
            a.nid = n
            a.id = 'n'+str(n)
            n += 1

    postorder(a,assign_nid_util)


def assign_sid(a: PROGRAM) -> None:
    order: dict[str,int] = a.order

    def assign_sid_util(a: AST) -> None:
        nonlocal order

        if isinstance(a,VAR): 
            b = cast(VAR,a)
            if b.name in list(order):
                b.sid = order[b.name]
            else:
                raise RuntimeError('Referenced signal not defined')

    postorder(a,assign_sid_util)


def type_check(a: AST) -> bool:
    status: bool = True

    def type_check_util(a: AST) -> None: # TODO error messages
        nonlocal status
        c: AST

        # enforce no mixed-time formulas
        if isinstance(a,TL_FT_OP):
            for c in a.children:
                status = status and c.formula_type != FormulaType.PT
            a.formula_type = FormulaType.FT
        elif isinstance(a,TL_PT_OP):
            for c in a.children:
                status = status and c.formula_type != FormulaType.FT
            a.formula_type = FormulaType.PT
        else:
            # not a TL op, propagate formula type from children
            for c in a.children:
                if c.formula_type == FormulaType.FT or c.formula_type == FormulaType.PT:
                    a.formula_type = c.formula_type


        if isinstance(a,LIT) or isinstance(a,PROGRAM):
            pass
        elif isinstance(a,SPEC):
            child = cast(EXPR,a.children[0])
            if not child._type == Type.BOOL:
                status = False
        elif isinstance(a,REL_OP):
            # both operands must be literals of same type
            lhs = a.children[0]
            rhs = a.children[1]
            status = status and isinstance(lhs,LIT) and isinstance(rhs,LIT)
            status = status and lhs._type == rhs._type
            a._type = Type.BOOL
        elif isinstance(a,LOG_OP):
            for c in a.children:
                status = status and c._type == Type.BOOL
            a._type = Type.BOOL
        elif isinstance(a,TL_OP):
            for c in a.children:
                status = status and c._type == Type.BOOL
            status = status and a.interval.lb <= a.interval.ub
            a._type = Type.BOOL
        else:
            status = False

    postorder(a,type_check_util)
    return status


def optimize_cse(a: PROGRAM) -> None:
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
            
    postorder(a,optimize_cse)


def gen_atomic_asm(a: PROGRAM) -> str:
    if not type_check(a):
        return ''

    s: str = ''
    visited: dict[int,ATOM] = {}
    a_num: int = 0

    def gen_atomic_asm_util(a: AST) -> None:
        nonlocal s
        nonlocal visited
        nonlocal a_num

        c: int
        for c in range(0,len(a.children)):
            child = a.children[c]
            i = id(child)

            if isinstance(a,REL_OP):
                return

            if isinstance(child,REL_OP):
                if i in list(visited):
                    a.children[c] = visited[i]
                else:
                    tmp = cast(REL_OP,child)
                    s += tmp.asm(a_num)
                    visited[i] = ATOM('a'+str(a_num),a_num)
                    a.children[c] = visited[i]
                    a_num += 1
            elif isinstance(child,VAR): 
                if i in list(visited):
                    a.children[c] = visited[i]
                else:
                    tmp = cast(VAR,child)
                    s += tmp.asm(a_num)
                    tmp = ATOM('a'+str(a_num),a_num)
                    visited[i] = tmp
                    a.children[c] = tmp
                    a_num += 1

    preorder(a,gen_atomic_asm_util)
    return s


def compute_scq_size(a: AST) -> None:
    
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

    preorder(a,compute_scq_size_util)


def gen_scq_assembly(a: AST) -> str:
    s: str = ''
    pos: int = 0

    compute_scq_size(a)

    def gen_scq_assembly_util(a: AST) -> None:
        nonlocal s
        nonlocal pos

        if isinstance(a,PROGRAM) or isinstance(a,CONST):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        s += str(start_pos) + ' ' + str(end_pos) + '\n'

    postorder(a,gen_scq_assembly_util)
    return s


def gen_assembly(a: PROGRAM) -> list[str]:
    if not type_check(a):
        print('failed type check')
        return ['','n0: end sequence','n0: end sequence','']

    assign_sid(a)
    optimize_cse(a)

    atomic_asm: str = gen_atomic_asm(a)

    assign_nid(a)

    visited: list[int] = []
    ft_asm: str = ''

    def gen_assembly_util(a: AST) -> None:
        nonlocal ft_asm
        nonlocal visited

        if isinstance(a, VAR) or isinstance(a, REL_OP):
            raise RuntimeError('Atomics not resolved; call \'gen_atomic_eval\' before \'gen_assembly\'')

        if isinstance(a,CONST):
            return

        if not a.nid in visited:
            ft_asm += a.asm()
            visited.append(a.nid)

    postorder(a,gen_assembly_util)

    scq_asm = gen_scq_assembly(a)

    return [atomic_asm,ft_asm,'n0: end sequence',scq_asm]


def parse(input) -> list[PROGRAM]:
    lexer = C2POLexer(InputStream(input))
    stream = CommonTokenStream(lexer)
    parser = C2POParser(stream)
    parse_tree = parser.start()

    # print(parse_tree.toStringTree(recog=parser))
    
    v = Visitor()
    return v.visit(parse_tree)


def compile(input, output_path) -> None:
    progs = parse(input)
    atomic_asm,ft_asm,pt_asm,ftscq_asm = gen_assembly(progs[0])

    with open(output_path+'at.asm','w') as f:
        f.write(atomic_asm)
    with open(output_path+'ft.asm','w') as f:
        f.write(ft_asm)
    with open(output_path+'pt.asm','w') as f:
        f.write(pt_asm)
    with open(output_path+'ftscq.asm','w') as f:
        f.write(ftscq_asm)

    assemble_at(output_path+'at.asm',output_path,'False')

    assemble_ft(output_path+'ft.asm',output_path+'ftscq.asm','4',output_path,'False')
    assemble_pt(output_path+'pt.asm','4',output_path,'False')
