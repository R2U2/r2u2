"""
We closely follow the pseudocode on page 8 of:
https://dl.acm.org/doi/pdf/10.1145/3434304
"""
from __future__ import annotations
from dataclasses import dataclass, field
from c2po.ast import *


@dataclass
class ENode():
    node: C2POExpression
    children: List[EClass]

    def __hash__(self) -> int:
        return hash(self.node)

@dataclass
class EClass():
    id: int
    members: Set[ENode]
    parents: Set[ENode] = field(default_factory=set)

    def __hash__(self) -> int:
        return self.id


class EGraph():

    def __init__(self, exprs: Set[C2POExpression]) -> None:
        self.leader: Dict[EClass, ENode] = {}
        self.eclass: Dict[C2POExpression, EClass] = {}
        self.cur_id = 1

        # check isinstance(n, C2POExpression) for type consistency, they should all be C2POExpressions anyway
        for node in [n for expr in exprs for n in postorder(expr) if isinstance(n, C2POExpression)]:
            self.add(node)

    def add(self, expr: C2POExpression) -> EClass:
        eclass = self.find(expr)
        if eclass:
            return eclass
        
        new_enode = ENode(expr, [self.add(c) for c in expr.children if isinstance(c, C2POExpression)])
        new_eclass = EClass(self.cur_id, {new_enode}, set())
        self.cur_id += 1

        self.eclass[expr] = new_eclass

        return new_eclass

    def find(self, expr: C2POExpression) -> Optional[EClass]:
        if expr in self.eclass: # this is a syntactic check
            return self.eclass[expr]
        return None

    def merge(self, id1: int, id2: int):
        pass

    def __str__(self) -> str:
        s = "\n".join([f"{str(e)} : {ecls.id}" for e,ecls in self.eclass.items()])
        return s


