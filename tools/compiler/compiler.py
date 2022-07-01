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

class Compiler():

    def __init__(self, output_path, input, optimize=True):
        # initialize variables
        self.output_path: str = output_path
        self.input = input
        self.optimize = optimize
        self.status = True
        self.order: dict[str,int] = {}
        # Check to see if the output directory exists
        if(not os.path.isdir(output_path)):
            os.mkdir(output_path)


    def parse(self, input) -> list[PROGRAM]:
        lexer = C2POLexer(InputStream(input))
        stream = CommonTokenStream(lexer)
        parser = C2POParser(stream)
        parse_tree = parser.start()

        # print(parse_tree.toStringTree(recog=parser))
        
        v = Visitor()
        return v.visit(parse_tree)


    def compile(self):
        progs = self.parse(self.input)
        atomic_asm,ft_asm,pt_asm,ftscq_asm = gen_assembly(progs[0])

        with open(self.output_path+'at.asm','w') as f:
            f.write(atomic_asm)
        with open(self.output_path+'ft.asm','w') as f:
            f.write(ft_asm)
        with open(self.output_path+'pt.asm','w') as f:
            f.write(pt_asm)
        with open(self.output_path+'ftscq.asm','w') as f:
            f.write(ftscq_asm)

        assemble_at(self.output_path+'at.asm',self.output_path,'False')

        assemble_ft(self.output_path+'ft.asm',self.output_path+'ftscq.asm','4',self.output_path,'False')
        assemble_pt(self.output_path+'pt.asm','4',self.output_path,'False')


    

# def main(args):

#     binary_dir = args.output_dir + 'binary_files/'

#     if not os.path.isdir(args.output_dir):
#         os.mkdir(args.output_dir)

#     # Remove binary files directory, if it exists, and start fresh
#     if os.path.isdir(binary_dir):
#         shutil.rmtree(binary_dir)

#     # If the argument is a valid file,
#     #if(os.path.isfile(__AbsolutePath__ + mltl)):
#     #    MLTL = open(args.mltl,'r').read()
#     if(os.path.isfile(args.mltl)):
#         MLTL = open(args.mltl,'r').read()
#     else:
#         MLTL = args.mltl

#     mltl_compiler = Compiler(binary_dir, MLTL)
#     # mltl_compiler.preprocess()

#     print('************************** FT ASM **************************')

#     mltl_compiler.compile()
#     return

# if __name__ == "__main__":
#     parser = argparse.ArgumentParser()
#     parser.add_argument("mltl",
#                         help="file where mltl formula are stored or literal mltl formula")
#     parser.add_argument("--config-file", default=__AbsolutePath__+'r2u2.conf',
#                         help="path to configuration file")
#     parser.add_argument("--header-file",
#                         default=__AbsolutePath__+'gen_files/config_files/R2U2Config.h',
#                         help="path to configuration header file, uses this file to detect if recompilation is needed")
#     parser.add_argument("--output-dir", default=__AbsolutePath__+'gen_files/',
#                         help="location where files will be generated")
#     parser.add_argument("--compiler-dir", default=__AbsolutePath__+'Compiler/',
#                         help="location where compiler programs will be called from")
#     parser.add_argument("--assembler-dir",default=__AbsolutePath__+'Assembler/',
#                         help="location where assembly and configuration programs will be called from")
#     parser.add_argument("--no-binaries", action="store_true",
#                         help="generate config.c file in place of binaries")
#     parser.add_argument("--no-symbolic-names", action="store_true",
#                         help="restricts use of symbolic names for atomics and signals")
#     args = parser.parse_args()
#     main(args)