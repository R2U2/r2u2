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

    def __eq__(self, __value: object) -> bool:
        """ENodes "f(a,b)" and "g(c,d)" are equivalent iff
            f == g and eclass[a].id == eclass[c.id] and eclass[b].id == eclass[d].id"""
        return (
            isinstance(__value, ENode) and 
            self.node.symbol == __value.node.symbol and
            all(c1.id  == c2.id for (c1,c2) in zip(self.children, __value.children))
        )

    def __hash__(self) -> int:
        """An ENode for "f(a,b)" has a hash (without spaces):
            "f eclass[a].id eclass[b].id" """
        return hash("".join([self.node.symbol] + [str(c.id) for c in self.children]))

@dataclass
class EClass():
    id: int
    members: Set[ENode]
    parents: Set[ENode]

    def __hash__(self) -> int:
        return self.id


class EGraph():

    def __init__(self, exprs: Set[C2POExpression]) -> None:
        self.eclass: Dict[C2POExpression, EClass] = {}
        self.enode: Dict[C2POExpression, ENode] = {}
        self.cur_id = 1

        # check isinstance(n, C2POExpression) for type consistency, they should all be C2POExpressions anyway
        for node in [n for expr in exprs for n in postorder(expr) if isinstance(n, C2POExpression)]:
            self.add(node)

    def add(self, expr: C2POExpression) -> EClass:
        """Adds `expr` and its children to the EGraph, if `expr` is not already present."""
        if expr in self.eclass: # this is a syntactic check
            return self.eclass[expr]
        
        new_enode = ENode(expr, [self.add(c) for c in expr.children if isinstance(c, C2POExpression)])
        new_eclass = EClass(self.cur_id, {new_enode}, set())
        self.cur_id += 1

        self.enode[expr] = new_enode
        self.eclass[expr] = new_eclass

        return new_eclass

    # def find(self, expr: C2POExpression) -> Optional[EClass]:
    #     """Returns the EClass for `expr` if it is in the EGraph, otherwise returns `None`. `expr` is considered in the EGraph if there is a syntactically identical C2POExpression to `expr` in the EGraph."""
    #     if expr in self.eclass: # this is a syntactic check
    #         return self.eclass[expr]
    #     return None

    def merge(self, eclass1: EClass, eclass2: EClass) -> EClass:
        if eclass1.id == eclass2.id:
            return eclass1

        # TODO: update self.eclass for each member

        # TODO: check if any parents now must be merged
        # consider a case where we have 3 eclasses with one node each:
        #    1: {f(a,b)} 
        #    2: {f(a,c)}
        #    3: {a}
        #    4: {b}
        #    5: {c}
        # Then we merge 4 and 5 to obtain:
        #    1: {f(a,b)} 
        #    2: {f(a,c)}
        #    3: {a}
        #    4: {b,c}
        # But now 1 and 2 are actually equivalent, we need to merge them as well:
        #    1: {f(a,b)} 
        #    3: {a}
        #    4: {b,c}

        return EClass(
            eclass1.id, 
            eclass1.members | eclass2.members, 
            eclass1.parents | eclass2.parents
        )

    def __str__(self) -> str:
        s = "\n".join([f"{str(e)} : {ecls.id}" for e,ecls in self.eclass.items()])
        return s


