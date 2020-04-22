## Description: Double linked observer syntax tree
## Author: Pei Zhang
class AST_node():
    cnt2node = {}
    node_cnt = 0

    def __init__(self):
        self.child = []
        self.pre = None
        AST_node.cnt2node[AST_node.node_cnt] = self
        AST_node.node_cnt += 1

    def add(self, node):
        if (node==None):
            return
        self.child.append(node)
        node.pre = self

    @staticmethod
    def reset():
        cnt2node = {}
        node_cnt = 0

  # var alias to left and right
    @property
    def left(self):
        return None if len(self.child)==0 else self.child[0]
    @left.setter
    def left(self, val):
        if (len(self.child)==0):
            self.child.append(val)
        else:
            self.child[0] = val
    @property
    def right(self):
        return None if len(self.child)<2 else self.child[1]
    @right.setter
    def right(self, val):
        if (len(self.child)<2):
            self.child.append(val)
        else:
            self.child[1] = val


class PROGRAM(AST_node): # PROGRAM is always the top AST node
    sm_cnt = 0
    def __init__(self):
        super().__init__()
        self.type = 'PROG'
        self.name = 'PROGRAM'

    def add(self, statement):
        super().add(statement)
        PROGRAM.sm_cnt += 1


class STATEMENT(AST_node):
    formula_cnt = 0
    def __init__(self, ob):
        super().__init__()
        self.type = 'SM'
        self.name = 'STATEMENT'
        self.add(ob)
        self.ob = ob
        self.formula_num = STATEMENT.formula_cnt
        STATEMENT.formula_cnt += 1
        
    def gen_assembly(self, s):
        substr = 'end '+self.child[0].hook
        self.hook = 's'+str(Observer.line_cnt)
        s += self.hook+": "+substr+ ' (FORM-'+str(self.formula_num)+')' + '\n'
        Observer.line_cnt += 1
        return s
        

class Observer(AST_node):
    line_cnt = 0 #static var to record line number
    # cnt2observer = {}
    # operator_cnt = 0
    def __init__(self, left=None, right=None):
        super().__init__()
        # self.type = 'OBSERVER'
        self.add(left)
        self.add(right)
        # self.left = left
        # self.right = right

        #self.pre = None
        self.hook = -1
        self.scq_size = 1
        self.bpd = 0 # best-case propogation delay
        self.wpd = 0 # worst-case propogation delay
        # Observer.cnt2observer[Observer.operator_cnt] = self
        # Observer.operator_cnt += 1

    @staticmethod
    def reset():
        # Observer.cnt2observer = {}
        # Observer.operator_cnt = 0
        Observer.line_cnt = 0

    def gen_assembly(self, s, substr):
        self.hook = 's'+str(Observer.line_cnt)
        s += self.hook+": "+substr+'\n'
        Observer.line_cnt += 1
        return s

class ATOM(Observer):
    def __init__(self, name):
        super().__init__()
        self.type = 'ATOM'
        self.tag = 0
        self.name = name

    def gen_assembly(self, s):
        substr = "load "+self.name
        s = super().gen_assembly(s, substr)
        return s
        
class BOOL(Observer):
    def __init__(self, tOrF):
        super().__init__()
        self.scq_size = 0
        self.type = 'BOOL'
        self.name = tOrF.upper()
        self.tag = -1
        self.hook = tOrF.upper()

    def gen_assembly(self, s):
        pass

class NEG(Observer):
    def __init__(self, left):
        super().__init__(left)
        self.type = 'NEG'
        self.name = 'NEG'
        self.tag = 1
        self.left.pre = self

    def gen_assembly(self, s):
        substr = "not "+self.left.hook
        s = super().gen_assembly(s, substr)
        return s

class YESTERDAY(Observer):
    def __init__(self, left):
        super().__init__(left)
        self.type = 'YES'
        self.name = 'YESTERDAY'
        self.tag = 1
        self.left.pre = self

    def gen_assembly(self, s):
        substr = "yesterday "+self.left.hook
        s = super().gen_assembly(s, substr)
        return s

class EQ(Observer):
    def __init__(self, left, right):
        super().__init__(left, right)       
        self.type = 'EQ'
        self.name = 'EQ'
        self.tag = 2
        self.left.pre, self.right.pre = self, self

    def gen_assembly(self, s):
        substr = "eq "+self.left.hook+" "+self.right.hook
        s = super().gen_assembly(s, substr)
        return s

class IMPLY(Observer):
    def __init__(self, left, right):
        super().__init__(left, right)       
        self.type = 'IMPLY'
        self.name = 'IMPLY'
        self.tag = 2
        self.left.pre, self.right.pre = self, self

    def gen_assembly(self, s):
        substr = "imply "+self.left.hook+" "+self.right.hook
        s = super().gen_assembly(s, substr)
        return s

class AND(Observer):
    def __init__(self, left, right):
        super().__init__(left, right)       
        self.type = 'AND'
        self.name = 'AND'
        self.tag = 2
        self.left.pre, self.right.pre = self, self

    def gen_assembly(self, s):
        substr = "and "+self.left.hook+" "+self.right.hook
        s = super().gen_assembly(s, substr)
        return s

class OR(Observer):
    def __init__(self, left, right):
        super().__init__(left, right)       
        self.type = 'OR'
        self.name = 'OR'
        self.tag = -2
        self.left.pre, self.right.pre = self, self

    def gen_assembly(self, s):
        substr = "or "+self.left.hook+" "+self.right.hook
        s = super().gen_assembly(s, substr)
        return s

class GLOBAL(Observer):
    def __init__(self, left, ub, lb=0):
        super().__init__(left)
        self.type = 'GLOBAL'
        self.tag = 3
        self.name = 'G['+str(lb)+','+str(ub)+']'
        self.lb, self.ub = lb, ub
        self.left.pre = self

    def gen_assembly(self, s):
        # if(self.lb==0): # boxdot no longer support in VHDL
        #   substr = "boxbox "+self.left.hook+" "+str(self.ub)
        # else:
        substr = "boxdot "+self.left.hook+" "+str(self.lb)+" "+str(self.ub)
        s = super().gen_assembly(s, substr)
        return s

class SINCE(Observer):
    def __init__(self, left, right, ub, lb=0):
        super().__init__(left, right)
        self.type = 'SINCE'
        self.tag = 4
        self.name = 'S['+str(lb)+','+str(ub)+']'
        self.lb, self.ub = lb, ub
        self.left.pre, self.right.pre = self, self

    def gen_assembly(self, s):
        substr = "since "+self.left.hook+" "+self.right.hook+" "+str(self.lb)+" "+str(self.ub)
        s = super().gen_assembly(s, substr)
        return s

class FUTURE(Observer):
    def __init__(self, left, ub, lb=0):
        super().__init__(left)
        self.type = 'FUTURE'
        self.tag = 3
        self.name = 'F['+str(lb)+','+str(ub)+']'
        self.lb, self.ub = lb, ub
        self.left.pre = self

    def gen_assembly(self, s):
        # if(self.lb==0): # boxdot no longer support in VHDL
        #   substr = "boxbox "+self.left.hook+" "+str(self.ub)
        # else:
        substr = "future "+self.left.hook+" "+str(self.lb)+" "+str(self.ub)
        s = super().gen_assembly(s, substr)
        return s

class ONCE(Observer):
    def __init__(self, left, ub, lb=0):
        super().__init__(left)
        self.type = 'ONCE'
        self.tag = 3
        self.name = 'O['+str(lb)+','+str(ub)+']'
        self.lb, self.ub = lb, ub
        self.left.pre = self

    def gen_assembly(self, s):
        # if(self.lb==0): # boxdot no longer support in VHDL
        #   substr = "boxbox "+self.left.hook+" "+str(self.ub)
        # else:
        substr = "once "+self.left.hook+" "+str(self.lb)+" "+str(self.ub)
        s = super().gen_assembly(s, substr)
        return s


class HISTORICALLY(Observer):
    def __init__(self, left, ub=0, lb=0):
        super().__init__(left)
        self.type = 'HIS'
        self.tag = 4
        self.name = 'H['+str(lb)+','+str(ub)+']'
        self.lb, self.ub = lb, ub
        self.left.pre = self

    def gen_assembly(self, s):
        substr = "his "+self.left.hook+" "+str(self.lb)+" "+str(self.ub)
        s = super().gen_assembly(s, substr)
        return s


class UNTIL(Observer):
    def __init__(self, left, right, ub, lb=0):
        super().__init__(left, right)
        self.type = 'UNTIL'
        self.tag = 4
        self.name = 'U['+str(lb)+','+str(ub)+']'
        self.lb, self.ub = lb, ub
        self.left.pre, self.right.pre = self, self

    def gen_assembly(self, s):
        substr = "until "+self.left.hook+" "+self.right.hook+" "+str(self.lb)+" "+str(self.ub)
        s = super().gen_assembly(s, substr)
        return s

class RELEASE(Observer):
    def __init__(self, left, right, ub, lb=0):
        super().__init__(left, right)
        self.type = 'RELEASE'
        self.tag = 4
        self.name = 'U['+str(lb)+','+str(ub)+']'
        self.lb, self.ub = lb, ub
        self.left.pre, self.right.pre = self, self

    def gen_assembly(self, s):
        substr = "release "+self.left.hook+" "+self.right.hook+" "+str(self.lb)+" "+str(self.ub)
        s = super().gen_assembly(s, substr)
        return s
