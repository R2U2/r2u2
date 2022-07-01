## Description: 1. optimize the AST; 2. assign SCQ size; 3. generate assembly
## Author: Chris Johannsen
import os
import shutil
import argparse

from antlr4 import InputStream, CommonTokenStream

from .ast import *
from .parser.C2POLexer import C2POLexer
from .parser.C2POParser import C2POParser
from .visitor import Visitor
from .assembler.atas import assemble_at
from .assembler.ftas import assemble_ft
from .assembler.ptas import assemble_pt

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'

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
