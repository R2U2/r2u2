from c2po.ast import *

class DisjointSet():

    def __init__(self):
        self.leader = {}
        self.group  = {}

    def add(self, node: C2POExpression):
        pass

    def find(self, node: C2POExpression):
        return self.leader[node]

"""
For rewrite rule optimizations -- will need to explicitly represent the set of
satisfying traces for a given expression to use as a hash. 

Looked into using regexes, but checking whether two sets of regexes are
equivalent is nontrivial. Note, eac MLTL formula is represented by a *set* of
regexes.
"""