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

    def __init__(self, output_path, mltl optimize_cse=True, Hp=0, echo=True):
        # initialize variables
        self.optimize = optimize_cse
        self.output_path = output_path
        self.Hp = Hp
        self.atomics = []
        self.signals = []
        self.labels = []
        self.status = True
        self.echo = echo
        self.mltl
        # Check to see if the output directory exists
        if(not os.path.isdir(output_path)):
            os.mkdir(output_path)


    def parse(self, input):
        lexer = MLTLLexer(InputStream(input))
        stream = CommonTokenStream(lexer)
        parser = MLTLParser(stream)
        parse_tree = parser.program()
        print(parse_tree.toStringTree(recog=parser))
        visitor = Visitor(self.ref_atomics)
        visitor.visit(parse_tree)
        return visitor


    def compile_ft(self, asm_filename):
        AST_node.reset()
        Observer.reset()

        ft = ''
        for line in self.mltl.split(';'):
            line = line.strip('\n ')
            # Ignore lines that are blank
            if(re.fullmatch('\s*', line)):
                continue
            if(re.search('[GFUR]',line) and re.search('[YHOS]',line)):
                # Check if line is mixed FT/PT
                print('ERROR: mixed time operators used in formula ' + line)
                print('Ignoring formula')
                continue
            if(re.search('[GFUR]',line)):
                # line is valid FT
                ft += line + ';\n'
            if(re.search('[YHOS]',line)):
                # line is valid pt, need to keep track of line numbers
                ft += '\n'

        # Parse the input and generate AST
        visitor = self.parse(ft)
        if not visitor.status:
            print('ERROR: issue parsing FT')
            self.status = False
            return

        self.gen_assembly(asm_filename)

    def compile_pt(self, asm_filename):
        AST_node.reset()
        Observer.reset()

        pt = ''
        for line in self.mltl.split(';'):
            line = line.strip('\n ')
            # Ignore lines that are blank
            if(re.fullmatch('\s*', line)):
                continue
            if(re.search('[GFUR]',line) and re.search('[YHOS]',line)):
                # Check if line is mixed FT/PT
                print('ERROR: mixed time operators used in formula ' + line)
                print('Ignoring formula')
                continue
            if(re.search('[YHOS]',line)):
                # line is valid PT
                pt += line + ';\n'
            if(re.search('[GFUR]',line)):
                # line is valid FT, need to keep track of line numbers
                pt += '\n'

        # Parse the input and generate AST
        visitor = self.parse(pt)
        if not visitor.status:
            print('ERROR: issue parsing FT')
            self.status = False
            return

        self.gen_assembly(asm_filename)


    def gen_assembly(asm_filename):
        self.asm = ""
        self.ast = AST_node.ast
        self.top = self.ast[0]
        if(self.optimize):
            self.optimize_cse()
        self.valid_node_set = self.sort_node()
        self.queue_size_assign(self.Hp, asm_filename)
        self.mltl_gen_assembly(asm_filename)


    def at_compile(self, at, asm_filename, alias_filename):
        # Parse the input and generate AST
        visitor = self.parse(at)

        if not visitor.status:
            print('ERROR: issue parsing AT')
            self.status = False
            return

        for atom in visitor.mapped_atomics:
            self.mapped_atomics.append(atom)

        for signal in visitor.signals:
            self.signals.append(signal)

        self.at_gen_assembly(visitor.at_instr, asm_filename)

        self.gen_alias_file_sigs(alias_filename)


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


    def at_gen_assembly(self, instructions, filename):
        s = ''

        # Unmapped atomics in the form 'a\d+'
        # Treat as a boolean
        for atom in self.ref_atomics:
            if atom not in self.mapped_atomics:
                if not re.search('a\d+', atom) is None:
                    # \d+ refers to index of the signal we want to refer
                    num = re.search('\d+', atom).group()
                    if not int(num) in self.sig_indices:
                        self.sig_indices.append(int(num))

                    s += 'a' + str(self.ref_atomics.index(atom)) + ': bool s' +\
                            num + ' 0 == 1\n'
                else:
                    print('ERROR: Atom ' + atom + ' referenced but not mapped')
                    self.status = False

        # Mapped atomics with signal in form 's\d+'
        for atom, instr in instructions.items():
            if atom in self.ref_atomics:
                if re.match('s\d+', instr[1]):
                    # atom name must be in valid assembly form ('a\d+')
                    a = 'a' + str(self.ref_atomics.index(atom))
                    # map to associated signal index
                    sig_index = int(re.search('\d+', instr[1]).group(0))

                    s += a + ': ' + instr[0] + ' s' + str(sig_index) + ' ' + \
                        instr[2] + ' ' + instr[3] + ' ' + instr[4] + '\n'

        # Mapped atomics with aliased signal name
        for atom, instr in instructions.items():
            if atom in self.ref_atomics:
                if not re.match('s\d+', instr[1]):
                    # atom name must be in valid assembly form ('a\d+')
                    a = 'a' + str(self.ref_atomics.index(atom))

                    # Assign signal mapping an index not in use by another atomic
                    self.sig_indices.sort()
                    min_sig = 0
                    for sig in self.sig_indices:
                        if sig != min_sig:
                            break
                        else:
                            min_sig += 1
                    self.sig_indices.append(min_sig)
                    sig_index = min_sig

                    s += a + ': ' + instr[0] + ' s' + str(sig_index) + ' ' + \
                        instr[2] + ' ' + instr[3] + ' ' + instr[4] + '\n'
            else:
                print('WARNING: Atom ' + atom + ' not referenced in MLTL, ignoring')

        s = s[:len(s)-1] # remove last newline

        if self.echo:
            print(s)

        with open(self.output_path+filename, 'a') as f:
            f.write(s)

    def gen_alias_file(self, filename):
        s = ''
        for label, line_num in self.labels:
            s += 'l ' + label + ' ' + str(line_num) + '\n'
        for signal, index in self.signals:
            s += 's ' + signal + ' ' + str(index) + '\n'
        for atom, index in self.atomics:
            s += 'a ' + atom + ' ' + str(index) + '\n'
        with open(self.output_path+filename, 'a') as f:
            f.write(s)
