## Description: 1. optimize the AST; 2. assign SCQ size; 3. generate assembly
## Author: Pei Zhang
from antlr4 import *
from .MLTLLexer import MLTLLexer
from .MLTLParser import MLTLParser
from .visitor import Visitor
from .AST import *
import os
import re

asmFileName = ""
class Compiler():

    def __init__(self, output_path, mltl, optimize_cse=True, Hp=0, echo=True):
        # initialize variables
        self.output_path = output_path
        self.mltl = mltl
        self.optimize = optimize_cse
        self.Hp = Hp
        self.echo = echo
        self.atomics = {}
        self.signals = {}
        self.labels = {}
        self.contracts = {}
        self.at_instructions = {}
        self.status = True
        # Check to see if the output directory exists
        if(not os.path.isdir(output_path)):
            os.mkdir(output_path)
        # make first pass of input to preprocess identifiers and contracts
        self.preprocess()


    def parse(self, input):
        AST_node.reset()
        Observer.reset()
        lexer = MLTLLexer(InputStream(input))
        stream = CommonTokenStream(lexer)
        parser = MLTLParser(stream)
        parse_tree = parser.program()
        #print(parse_tree.toStringTree(recog=parser))
        visitor = Visitor(self.atomics, self.signals, self.labels)
        visitor.visit(parse_tree)
        return visitor


    def preprocess(self):
        visitor = self.parse(self.mltl)
        if not visitor.status:
            print('ERROR: issue parsing MLTL')
            self.status = False
            return
        self.atomics = visitor.atomics
        self.signals = visitor.signals
        self.labels = visitor.labels
        self.contracts = visitor.contracts

        # Add formulas for contract handling
        # First count number of formulas which are not in contracts
        formula_num = 0
        for line in self.mltl.split(';'):
            line = line.strip('\n ')
            # Ignore lines that are blank, contracts, or atomic bindings
            if re.fullmatch('\s*', line) or re.search('=>',line) or re.search(':=',line):
                continue
            # Check if line is mixed FT/PT
            if re.search('^[^\#]*[GFUR]\[',line) and \
               re.search('^[^\#]*[YHOS]\[',line):
                continue
            formula_num += 1

        for contract, formulas in self.contracts.items():
            self.contracts[contract] = formula_num
            self.mltl += formulas[0] + ';\n'
            self.mltl += formulas[0] + '->' + formulas[1] + ';\n'
            self.mltl += formulas[0] + '&' + formulas[1] + ';\n'
            formula_num += 3

        # Assign the atomics valid indices
        for atom, index in self.atomics.items():
            if re.match('a\d+',atom):
                idx = re.search('\d+',atom).group()
                self.atomics[atom] = int(idx)
                self.at_instructions[atom] = ['bool','s'+idx,'0','==','1']

        min_idx = 0
        for atom, index in self.atomics.items():
            if re.match('a\d+',atom):
                continue
            while min_idx in self.atomics.values():
                min_idx += 1
            if self.atomics[atom] == -2:
                print('WARNING: atomic referenced but not binded: ' + atom)
                self.at_instructions['a'+str(min_idx)] = \
                    ['bool','s'+str(min_idx),'0','==','1']
            self.atomics[atom] = min_idx

        # Assign the signals valid indices
        for signal, index in self.signals.items():
            if re.match('s\d+',signal):
                self.signals[signal] = int(re.search('\d+',signal).group())

        min_idx = 0
        for signal, index in self.signals.items():
            if re.match('s\d+',signal):
                continue
            if self.signals[signal] == -1:
                print('WARNING: signal referenced but not mapped: ' + signal)
                while min_idx in self.signals.values():
                    min_idx += 1
                self.signals[signal] = min_idx


    def compile_ft(self, asm_filename):
        AST_node.reset()
        Observer.reset()

        ft = ''
        for line in self.mltl.split(';'):
            line = line.strip('\n ')
            # Ignore lines that are blank, contracts, or bindings
            if re.fullmatch('\s*', line) or re.search('=>',line) or \
              re.search(':=',line):
                continue
            # Check if line is mixed FT/PT
            if re.search('^[^\#]*[GFUR]\[',line) and \
               re.search('^[^\#]*[YHOS]\[',line):
                print('ERROR: mixed time operators used in formula ' + line)
                print('Ignoring formula')
                continue
            # line is valid pt, need to keep track of line numbers
            if re.search('(^|\n)[^\#]*[YHOS]\[',line):
                ft += '\n'
                continue
            # line is valid FT or propositional logic
            ft += line + ';\n'

        # if no FT formulas in file, write empty asm
        if re.fullmatch('\s*',ft):
            f = open(self.output_path+'ft.asm','w+')
            f.write('s0: end sequence')
            f.close()
            print('s0: end sequence')
            f = open(self.output_path+'ftscq.asm','w+')
            f.write('0 0')
            f.close()
            return

        # Parse the input and generate AST
        visitor = self.parse(ft)
        if not visitor.status:
            print('ERROR: issue parsing FT')
            self.status = False
            return

        self.asm = ""
        self.ast = AST_node.ast
        self.top = self.ast[0]
        if(self.optimize):
            self.optimize_cse()
        self.valid_node_set = self.sort_node()
        self.queue_size_assign(self.Hp, asm_filename)
        self.mltl_gen_assembly(asm_filename)

    def compile_pt(self, asm_filename):
        AST_node.reset()
        Observer.reset()

        pt = ''
        for line in self.mltl.split(';'):
            line = line.strip('\n ')
            # Ignore lines that are blank, contracts, or bindings
            if re.fullmatch('\s*', line) or re.search('=>',line) or \
              re.search(':=',line):
                continue
            # Check if line is mixed FT/PT
            if re.search('^[^\#]*[GFUR]\[',line) and \
               re.search('^[^\#]*[YHOS]\[',line):
                print('ERROR: mixed time operators used in formula ' + line)
                print('Ignoring formula')
                continue
            # line is valid FT/propositional logic formula, need to keep track
            # of line numbers
            if not re.search('(^|\n)[^\#]*[YHOS]\[',line):
                pt += '\n'
                continue
            # line is valid PT
            pt += line + ';\n'

        # if no PT formulas in file, write empty asm
        if re.fullmatch('\s*',pt):
            f = open(self.output_path+'pt.asm','w+')
            f.write('s0: end sequence')
            f.close()
            print('s0: end sequence')
            return

        # Parse the input and generate AST
        visitor = self.parse(pt)
        if not visitor.status:
            print('ERROR: issue parsing FT')
            self.status = False
            return

        self.asm = ""
        self.ast = AST_node.ast
        self.top = self.ast[0]
        if(self.optimize):
            self.optimize_cse()
        self.valid_node_set = self.sort_node()
        self.queue_size_assign(self.Hp, asm_filename)
        self.mltl_gen_assembly(asm_filename)


    def compile_at(self, asm_filename):
        at = ''
        for line in self.mltl.split(';'):
            line = line.strip('\n ')
            # Ignore lines that are blank
            if re.fullmatch('\s*', line):
                continue
            if re.search(':=',self.mltl):
                at += line + ';\n'
            else:
                at += '\n'

        # Parse the input and generate AST
        visitor = self.parse(at)

        if not visitor.status:
            print('ERROR: issue parsing AT')
            self.status = False
            return

        for atom, instr in visitor.at_instr.items():
            self.at_instructions[atom] = instr

        self.at_gen_assembly(asm_filename)


    # Common subexpression elimination the AST
    def optimize_cse(self):
        # Map preorder traverse to observer node, use '(' and ')' to represent boundry
        if(len(self.ast)==0):
            return
        def preorder(root,m):
            if(root==None):
                return []
            link = ['(']
            link.extend([root.name])
            for c in root.child:
                if c:
                    link.extend(preorder(c,m))
            # link.extend(inorder(root.left,m))
            # link.extend([root.name])
            # link.extend(inorder(root.right,m))
            link.append(')')
            tup = tuple(link)
            if(tup in m):
                # find left of right branch of pre node
                parent = root.pre
                for i,c in enumerate(parent.child):
                    if c and c==root:
                        parent.child[i] = m[tup]
                # if(root.pre.left==root):
                #     root.pre.left = m[tup]
                # else:
                #     root.pre.right = m[tup]
            else:
                m[tup] = root
            return link

        # preorder traverse from the top node
        preorder(self.top,{})

    # TODO: logically optimize the AST, e.g., a0&a0->a0; a0&!a0=FALSE
    def optimize_logic(self):
        pass

    ###############################################################
    # Topological sort the node sequence, the sequence is stored in stack
    def sort_node(self):
        if(len(self.ast)==0):
            return []
        # top = self.ast[len(self.ast)-1]
        top = self.ast[0]
        # collect used node from the tree
        def checkTree(root, graph):
            if(root==None or root.type=='BOOL'):
                return
            if root not in graph:
                graph.append(root)
            for c in root.child:
                if c:
                    checkTree(c, graph)
            # checkTree(root.left, graph)
            # graph.add(root)
            # checkTree(root.right, graph)

        graph=[]
        checkTree(top,graph)

        def topologicalSortUtil(root, visited, stack):
            if(root!=None and root.type!='BOOL' and root not in visited):
                visited.add(root)
                # [topologicalSortUtil(i,visited,stack) for i in(root.left, root.right)]
                [topologicalSortUtil(i,visited,stack) for i in root.child]
                stack.insert(0,root)

        def topologicalSort(root, graph):
            visited = set()
            stack = []
            [topologicalSortUtil(node,visited,stack) for node in graph]
            return stack

        stack = topologicalSort(top,graph)
        return stack # parent to child

    ###############################################################
    # Assign the size for each queue
    def queue_size_assign(self,predLen,filename):
        stack = self.valid_node_set # parent to child
        vstack = stack[:] # copy the list
        vstack.reverse() # child to parent
        # compute propagation delay from bottom up
        def compute_propagation_delay():
            for n in vstack:
                if (not isinstance(n, Observer)):# the propogation delay only applies to Observer node
                    continue
                if(n.type=='ATOM'):
                    n.bpd = -1*predLen
                    n.scq_size = 1
                elif(n.type=='BOOL'):
                    n.bpd = 0
                    n.scq_size = 0
                elif( n.type in ('AND','OR','UNTIL','WEAK_UNTIL','RELEASE','IMPLY','EQ') ):
                    left, right = n.left, n.right
                    if(n.type in ('AND', 'OR', 'IMPLY','EQ')):
                        n.bpd, n.wpd = min(left.bpd, right.bpd), max(left.wpd, right.wpd)
                    else:
                        n.bpd, n.wpd = min(left.bpd, right.bpd)+n.lb, max(left.wpd, right.wpd)+n.ub
                else:
                    left = n.left
                    if(n.type == 'NEG' or n.type == 'YES'):
                        n.bpd, n.wpd = left.bpd, left.wpd
                    else:
                        n.bpd, n.wpd = left.bpd + n.lb, left.wpd + n.ub

        # compute scq size from top down
        def compute_scq_size():
            for n in vstack:
                # if (type(n)==STATEMENT):
                #     n.scq_size = 1
                #     n.left.scq_size = n.left.wpd-n.left.bpd+3 # special case for child node of END
                if (not isinstance(n, Observer)):
                    continue
                if(n.left and n.right):
                    left, right = n.left, n.right;
                    left.scq_size = max(right.wpd-left.bpd+1, left.scq_size)
                    right.scq_size = max(left.wpd-right.bpd+1, right.scq_size)
            for n in vstack:
                # added on May 9, 2020: to consider the extra space for potential output in one time stamp
                if (isinstance(n, Observer)):
                    n.scq_size += n.wpd-n.bpd+2


        def get_total_size():
            totsize = 0
            for n in vstack:
                if (isinstance(n, Observer) or isinstance(n,STATEMENT)):
                    #print(n.name,'  ',n,':  (',n.scq_size,')')
                    totsize += n.scq_size
            #print("Total SCQ entry: ", totsize)
            return totsize

        def generate_scq_size_file():
            # the scq size range [st_pos,ed_pos)
            s=""
            pos = 0
            for n in vstack:
                if ( isinstance(n, Observer) or isinstance(n,STATEMENT)):
                    st_pos = pos
                    ed_pos = st_pos+n.scq_size
                    pos = ed_pos
                    s += str(st_pos) + ' ' + str(ed_pos) + '\n'
            #if(self.asm_filename == "ft"):
            with open(self.output_path+'ftscq.asm',"w+") as f:
                f.write(s)

        compute_propagation_delay()
        compute_scq_size()
        if filename == 'ft.asm':
            generate_scq_size_file() # run this function if you want to generate c SCQ configuration file
        return get_total_size()


    # Generate assembly code
    def mltl_gen_assembly(self, filename):
        stack = self.valid_node_set[:]
        stack.reverse()
        s=""
        if(len(stack)==0):
            return s
        for node in stack:
            if (not (isinstance(node, Observer) or isinstance(node, STATEMENT))): # statement is used to generate the end command
                continue
            s = node.gen_assembly(s)
        s = s+'s'+str(Observer.line_cnt)+': end sequence' # append the end command

        if self.echo:
            print(s)

        with open(self.output_path+filename, 'w') as f:
            f.write(s)


    def at_gen_assembly(self, filename):
        s = ''
        # Mapped atomics with signal in form 's\d+'
        for atom, instr in self.at_instructions.items():
            s += atom + ': ' + instr[0] + ' ' + instr[1] + ' ' + \
                    instr[2] + ' ' + instr[3] + ' ' + instr[4] + '\n'
        s = s[:len(s)-1] # remove last newline
        if self.echo:
            print(s)
        with open(self.output_path+filename, 'a') as f:
            f.write(s)

    def gen_alias_file(self, filename):
        s = ''
        for label, num in self.labels.items():
            s += 'F ' + label + ' ' + str(num) + '\n'
        for contract, formula_num in self.contracts.items():
            s += 'C ' + contract + ' ' + str(formula_num) + ' ' + \
                str(formula_num+1) + ' ' + str(formula_num+2) + '\n'
        for signal, index in self.signals.items():
            s += 'S ' + signal + ' ' + str(index) + '\n'
        for atom, index in self.atomics.items():
            s += 'A ' + atom + ' ' + str(index) + '\n'
        with open(self.output_path+filename, 'a') as f:
            f.write(s)
