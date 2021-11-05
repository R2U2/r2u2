## Description: 1. optimize the AST; 2. assign SCQ size; 3. generate assembly
## Author: Pei Zhang, Chris Johannsen
import os

from antlr4 import InputStream, CommonTokenStream

from .AST import AST_node, Observer, STATEMENT
from .MLTLLexer import MLTLLexer
from .MLTLParser import MLTLParser
from .PreprocessVisitor import PreprocessVisitor
from .FTVisitor import FTVisitor
from .PTVisitor import PTVisitor
from .ATVisitor import ATVisitor


class Compiler():

    def __init__(self, output_path, mltl, valid_filters, optimize_cse=True, Hp=0, echo=True):
        # initialize variables
        self.output_path = output_path
        self.mltl = mltl
        self.valid_filters = valid_filters
        self.optimize = optimize_cse
        self.Hp = Hp
        self.echo = echo
        self.atomics = {}
        self.signals = {}
        self.formula_labels = {}
        self.contracts = {}
        self.at_instructions = {}
        self.ast = []
        self.top = AST_node()
        self.valid_node_set = []
        self.status = True
        # Check to see if the output directory exists
        if(not os.path.isdir(output_path)):
            os.mkdir(output_path)


    def parse(self, visitor, input):
        lexer = MLTLLexer(InputStream(input))
        stream = CommonTokenStream(lexer)
        parser = MLTLParser(stream)
        parse_tree = parser.program()
        #print(parse_tree.toStringTree(recog=parser))
        visitor.visit(parse_tree)


    # preprocess pass of input
    # resolves names, contracts, etc. and splits input into FT/PT/AT
    def preprocess(self):
        visitor = PreprocessVisitor()
        self.parse(visitor, self.mltl)

        if visitor.status == False:
            self.status = False
            return

        self.atomics = visitor.atomics
        self.signals = visitor.signals
        self.formula_labels = visitor.formula_labels
        self.contracts = visitor.contract_formula_nums
        self.def_sets = visitor.def_sets

        self.ft = visitor.ft
        self.pt = visitor.pt
        self.at = visitor.at


    def compile(self, visitor, input, asm_filename):
        AST_node.reset()
        Observer.reset()

        self.parse(visitor, input)

        self.asm = ""
        self.ast = AST_node.ast
        self.top = self.ast[0]
        if(self.optimize):
            self.optimize_cse()
        self.valid_node_set = self.sort_node()
        self.queue_size_assign(self.Hp, asm_filename)
        self.mltl_gen_assembly(asm_filename)


    def compile_ft(self, asm_filename):
        self.compile(FTVisitor(self.atomics),self.ft,asm_filename)


    def compile_pt(self, asm_filename):
        self.compile(PTVisitor(self.atomics),self.pt,asm_filename)


    def compile_at(self, asm_filename):
        visitor = ATVisitor(self.atomics, self.signals, self.valid_filters, self.def_sets)
        self.parse(visitor, self.at)

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
                    left, right = n.left, n.right
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
        set_instr = {}
        for atom, instr in self.at_instructions.items():
            # TODO need more robust way to order these
            if instr[0] == 'exactly_one_of':
                set_instr[atom] = instr
                continue

            s += 'a' + str(atom) + ': ' + str(instr[0]) + ' ' + str(instr[1]) + \
                ' ' + str(instr[2]) + ' '
            for arg in instr[3]:
                s += str(arg) + ' '
            s += '\n'

        # Put set AT instructions last since they depend on other atomic values
        for atom, instr in set_instr.items():
            s += 'a' + str(atom) + ': ' + str(instr[0]) + ' ' + str(instr[1]) + \
                ' ' + str(instr[2]) + ' '
            for arg in instr[3]:
                s += str(arg) + ' '
            s += '\n'

        s = s[:len(s)-1] # remove last newline
        if self.echo:
            print(s)
        with open(self.output_path+filename, 'a') as f:
            f.write(s)


    def gen_alias_file(self, filename):
        s = ''
        for label, num in self.formula_labels.items():
            s += 'F ' + label + ' ' + str(num) + '\n'
        for contract, formula_num in self.contracts.items():
            s += 'C ' + contract + ' ' + str(formula_num) + ' ' + \
                str(formula_num+1) + ' ' + str(formula_num+2) + '\n'
        for signal, index in self.signals.items():
            s += 'S ' + signal + ' ' + str(index) + '\n'
        for atom, index in self.atomics.items():
            s += 'A ' + atom + ' ' + str(index) + '\n'
        for set_name, atomics in self.def_sets.items():
            # Convert list of atomics in the set to their indicies.
            #
            # Here the list of atomics is in "a#" notation, but we want the
            # index, doing a lookup in the atomics dictionary is guaranteed to
            # be correct even in the pathological case of a# not being signal #
            # however, aliased signals will be listed by their given name, not
            # number. We get the best of both worlds at the cost of an extra
            # search by using the dictionary "get" method which is a key lookup
            # with optional default value.
            #
            # For example, if we have a bound atomic called "atom" which gets
            # assigned signal number 3 in preprocessing, the def_sets will list
            # "a3" as being a member of the set while the atomics dictionary
            # will have am entry for 'atom: 3' but not 'a: 3' so the
            # comprehension become atomics.get('a3', 3) which returns the
            # 2nd argument as a default and is correctly resolved to 3
            #
            # If we have a strong guarantee that the a# can never be incorrect
            # this can be replaced with just the string operation atom[1:]
            # alternatively we can list both names in the atomic dict during
            # preprocessing.
            atoms = [str(self.atomics.get(atom, atom[1:])) for atom in atomics[1]]
            s += 'R ' + set_name + ' ' + str(atomics[0]) + ' ' + ' '.join(atoms) + '\n'
        with open(self.output_path+filename, 'a') as f:
            f.write(s)
