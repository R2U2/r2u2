"""
We closely follow the pseudocode on page 8 of:
https://dl.acm.org/doi/pdf/10.1145/3434304
"""
from __future__ import annotations
from dataclasses import dataclass
from c2po.ast import *


@dataclass
class ENode():
    node: C2POExpression
    children: List[EClass]


@dataclass
class EClass():
    id: int
    members: Set[ENode]
    parents: Set[ENode] = set()

    def __hash__(self) -> int:
        return self.id


class EGraph():

    def __init__(self, exprs: Set[C2POExpression]):
        self.leader: Dict[EClass, ENode] = {}
        self.eclass:  Dict[C2POExpression, EClass]  = {}
        self.hashcons: Dict[ENode, EClass] = {}
        self.find: Dict[EClass, EClass] = {}
        self.cur_eid = 0

        # check isinstance(n, C2POExpression) for type consistency...they should all be C2POExpressions anyway
        # same for node's children below
        for node in [n for expr in exprs for n in postorder(expr) if isinstance(n, C2POExpression)]:
            self.add(ENode(node, [self.eclass[c] for c in node.children if isinstance(c, C2POExpression)]))

    def new_singleton_eclass(self, enode: ENode) -> EClass:
        self.cur_eid += 1
        return EClass(self.cur_eid-1, {enode})

    def canonicalize(self, enode: ENode) -> ENode:
        new_children = [self.find[c] for c in enode.children]
        return ENode(enode.node, new_children)

    def add(self, enode: ENode) -> EClass:
        enode = self.canonicalize(enode)

        if enode in self.hashcons:
            return self.hashcons[enode]

        eclass = self.new_singleton_eclass(enode)
        for child in enode.children:
            child.parents.add(enode)
        self.hashcons[enode] = eclass
        return eclass

    def merge(self, eclass1: EClass, eclass2: EClass) -> EClass:
        if self.find[eclass1] == self.find[eclass2]:
            return self.find[eclass1]
        
        return EClass(0, set())

