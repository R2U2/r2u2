"""
We closely follow the pseudocode on page 8 of:
https://dl.acm.org/doi/pdf/10.1145/3434304
"""
from __future__ import annotations
from dataclasses import dataclass
from c2po.ast import *


@dataclass
class ENode():
    expr: C2POExpression
    children: List[int]

    def __eq__(self, __value: object) -> bool:
        """ENodes `f(a,b)` and `g(c,d)` are equivalent iff
            f == g and eclass[a].id == eclass[c.id] and eclass[b].id == eclass[d].id"""
        return (
            isinstance(__value, ENode) and 
            self.expr.symbol == __value.expr.symbol and
            all(c1  == c2 for (c1,c2) in zip(self.children, __value.children))
        )

    def __hash__(self) -> int:
        """An ENode for `f(a,b)` has a hash:
            `f eclass[a].id eclass[b].id`"""
        return hash(" ".join([self.expr.symbol] + [str(c) for c in self.children]))

    def __str__(self) -> str:
        return f"ENode({self.expr.symbol}, {self.children})"

    def hash_subsume_or(self, eclass: Dict[ENode, int]) -> int:
        hash((
            type(self.expr),
            # type() 
        ))

        return 0


class UnionFind():
    """A UnionFind data structure for ints. Used to group equivalent EClass IDs together where `group` maps an int to the representative member of its set."""

    def __init__(self) -> None:
        self.group: Dict[int, int] = {}

    def add(self, id: int):
        if id in self.group:
            return
        self.group[id] = id

    def find(self, id: int) -> int:
        return self.group[id]

    def union(self, id1: int, id2: int) -> int:
        new_id = id1 if id1 < id2 else id2
        self.group[id1] = new_id
        self.group[id2] = new_id
        return new_id


class EGraph():

    def __init__(self, exprs: Set[C2POExpression]) -> None:
        self.eclass: Dict[ENode, int] = {}
        self.parents: Dict[int, Dict[ENode, int]] = {}
        self.worklist: set[int] = set()
        self.union_find: UnionFind = UnionFind()

        self.cur_eclass_id = 1

        # check isinstance(n, C2POExpression) for type consistency, they should all be C2POExpressions anyway
        for c2po_node in [n for expr in exprs for n in postorder(expr) if isinstance(n, C2POExpression)]:
            self.add(c2po_node)

    def enodes(self) -> Set[ENode]:
        return set(self.eclass.keys())

    def canonicalize(self, expr: C2POExpression) -> ENode:
        """Given a C2POExpression `f(a,b)`, returns `f(eclass[a].id, eclass[b].id)`"""
        children = [self.add(c) for c in expr.children if isinstance(c, C2POExpression)]
        return ENode(expr, children)

    def add(self, expr: C2POExpression) -> int:
        """Adds `expr` and its children to the EGraph, if `expr` is not already present."""
        enode = self.canonicalize(expr)

        if enode in self.eclass:
            return self.eclass[enode]
        
        new_eclass_id = self.cur_eclass_id
        self.cur_eclass_id += 1

        self.eclass[enode] = new_eclass_id
        self.union_find.add(new_eclass_id)
        self.parents[self.find(new_eclass_id)] = {}

        for child in enode.children:
            self.parents[child][enode] = new_eclass_id

        return new_eclass_id

    def find(self, id: int) -> int:
        return self.union_find.find(id)

    def members(self, id: int) -> Set[ENode]:
        canonical_id = self.find(id)
        return { enode for (enode, eclass_id) in self.eclass.items() if self.find(eclass_id) == canonical_id }

    def merge(self, eclass_id1: int, eclass_id2: int) -> int:
        if self.find(eclass_id1) == self.find(eclass_id2):
            return eclass_id1
            
        new_eclass_id = self.union_find.union(eclass_id1, eclass_id2)
        self.worklist.add(new_eclass_id)

        return new_eclass_id
 
    def rebuild(self):
        while len(self.worklist) != 0:
            todo = self.worklist.copy()
            self.worklist.clear()

            for eclass in {self.find(e) for e in todo} :
                self.repair(eclass)

    def repair(self, eclass: int):
        # TODO: check if any parents now must be merged (upward merge)
        # consider a case where we have 3 e-classes with one node each:
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
        for (parent, parent_eclass_id) in self.parents[eclass].items():
            del self.eclass[parent]
            new_parent = self.canonicalize(parent.expr)
            self.eclass[new_parent] = self.find(parent_eclass_id)

        new_parents: Dict[ENode, int] = {}
        for (parent, parent_eclass_id) in self.parents[eclass].items():
            new_parent = self.canonicalize(parent.expr)
            if new_parent in new_parents:
                # Note: merge puts the parent into self.worklist
                self.merge(parent_eclass_id, new_parents[new_parent])

            new_parents[parent] = self.find(parent_eclass_id)

        self.parents[eclass] = new_parents

    def __str__(self) -> str:
        s = "\n".join([f"{ecls} : {' '.join([str(m) for m in self.members(ecls)])}" for ecls in self.eclass.values()])
        return s


