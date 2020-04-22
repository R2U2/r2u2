## Description: 1. optimize the AST; 2. assign SCQ size; 3. generate assembly
## Author: Pei Zhang
# from .MLTLparse import *
# from .Observer import *
from . import MLTLparse
# from . import Observer
from .Observer import *

class Postgraph():
    def __init__(self,MLTL,optimize_cse=True,Hp=0):
        # Observer.Observer.line_cnt = 0 # clear var for multiple runs
        AST_node.reset()
        Observer.reset()
        # MLTLparse.cnt2node.clear() # clear var for multiple runs
        # MLTLparse.operator_cnt = 0 # clear var for multiple runs
        MLTLparse.parser.parse(MLTL)
        self.asm = ""
        if (MLTLparse.status=='syntax_err'):
            MLTLparse.status='pass'
            self.status = 'syntax_err'
            self.cnt2node = {}
            self.valid_node_set = []
            self.asm = ''
            return
        else:
            self.status = 'pass'
        # self.cnt2node = MLTLparse.cnt2node
        self.cnt2node = Observer.cnt2node
        # self.top = self.cnt2node[len(self.cnt2node)-1]
        self.top = self.cnt2node[0]
        if(optimize_cse):
            self.optimize_cse()
        self.valid_node_set = self.sort_node()
        self.queue_size_assign(Hp)
        self.gen_assembly()

    ###############################################################
    # Common subexpression elimination the AST
    def optimize_cse(self):
        # Map preorder traverse to observer node, use '(' and ')' to represent boundry
        if(len(self.cnt2node)==0):
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
        if(len(self.cnt2node)==0):
            return []
        # top = self.cnt2node[len(self.cnt2node)-1]
        top = self.cnt2node[0]
        # collect used node from the tree
        def checkTree(root, graph):
            if(root==None or root.type=='BOOL'):
                return
            graph.add(root)
            for c in root.child:
                if c:
                    checkTree(c, graph)
            # checkTree(root.left, graph)
            # graph.add(root)
            # checkTree(root.right, graph)

        graph=set()
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
    def queue_size_assign(self,predLen):
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
                if (type(n) != Observer):
                    continue
                if(n.left and n.right):
                    left, right = n.left, n.right;          
                    left.scq_size = max(right.wpd-left.bpd+1, left.scq_size)
                    right.scq_size = max(left.wpd-right.bpd+1, right.scq_size)

        def get_total_size():
            totsize = 0
            for n in vstack:
                if (type(n) != Observer):
                    continue
                print(n.name,'  ',n,':  (',n.scq_size,')')
                totsize += n.scq_size
            return totsize

        def generate_scq_size_file():
            # the scq size range [st_pos,ed_pos)
            s=""
            pos = 0
            for n in vstack:
                if (not isinstance(n, Observer)):
                    continue
                st_pos = pos
                ed_pos = st_pos+n.scq_size
                pos = ed_pos;
                s = s+'{0:08b}'.format(st_pos)+'{0:08b}'.format(ed_pos)+'\n'
            with open("tmp.ftscq","w+") as f:
                f.write(s)

        compute_propagation_delay()
        compute_scq_size()
        generate_scq_size_file() # run this function if you want to generate c SCQ configuration file
        return get_total_size()

    # Generate assembly code
    def gen_assembly(self): 
        stack = self.valid_node_set[:]
        stack.reverse()
        s=""
        if(len(stack)==0):
            return s
        for node in stack:
            if (not (isinstance(node, Observer) or isinstance(node, STATEMENT))): # statement is used to generate the end command
                continue
            print(node)
            s = node.gen_assembly(s)
        s = s+'s'+str(Observer.line_cnt)+': end sequence' # append the end command
        print(s)
        self.asm = s
        with open("tmp.ftasm","w+") as f:
            f.write(s)

