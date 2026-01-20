"""
Module for computing the optimal equivalent expression with respect to SCQ sizing using egglog.
"""
from __future__ import annotations
import pathlib
import dataclasses
import pprint
import signal   
from typing import Optional, NewType, Any
from c2po import cpt, log, util

try:
    import gurobipy as gp # type: ignore
    from gurobipy import GRB # type: ignore
except ImportError:
    raise ImportError("gurobipy is not installed")

ENodeID = NewType('ENodeID', str)
EClassID = NewType('EClassID', str)
Interval = NewType('Interval', tuple[int, int])

def timeout_handler(signum: int, frame: Any) -> None:
    raise TimeoutError("Gurobi optimization timed out")

@dataclasses.dataclass
class ENode:
    enode_id: ENodeID
    op: str
    interval: Optional[Interval]
    string: Optional[str]
    value: Optional[bool]
    child_eclass_ids: list[EClassID]
    eclass_id: EClassID

    @staticmethod
    def from_json(id: str, content: dict) -> ENode:
        """Return an `ENode` from egglog-generated JSON."""
        enode_content = content[id]
        child_eclass_ids = [
            content[c]["eclass"]
            for c in enode_content["children"]
            if "Interval" not in c and "String" not in c and "bool" not in c
        ]

        if enode_content["op"] in {"Global", "Future", "Until", "Release"}:
            """Temporal op "G[4,10] (...)" should look like:
            {
                "function-A-Global": {
                    "op": "Global",
                    "children": ["function-B-Interval", "function-C-Operand"],
                    "eclass": "MLTL-12",
                    ...
                }
                "function-B-Interval": {
                    "op": "Interval",
                    "children": ["i64-D", "i64-E"],
                    "eclass": "IntervalSort-F",
                    ...
                }
                "function-C-Operand": {
                    ...
                }
            }
            """
            interval_id = [i for i in content[id]["children"] if "Interval" in i]
            if len(interval_id) != 1:
                raise ValueError(f"no interval found for {id}")
            interval_id = interval_id[0]
            interval_content = content[interval_id]
            if len(interval_content["children"]) != 2:
                raise ValueError(f"invalid number of children for interval {interval_id} ({len(interval_content['children'])})")
            lb_id = interval_content["children"][0]
            ub_id = interval_content["children"][1]
            lb = int(content[lb_id]["op"])
            ub = int(content[ub_id]["op"])
            return ENode(
                ENodeID(id),
                enode_content["op"],
                Interval((lb, ub)),
                None,
                None,
                child_eclass_ids,
                enode_content["eclass"],
            )
        elif enode_content["op"] == "Var":
            """Variable "a0" should look like:
            {
                "function-A-Var": {
                    "op": "Var",
                    "children": ["String-B"],
                    "eclass": "MLTL-C",
                    ...
                }
                "String-B": {
                    "op": "a0",
                    "eclass": "String-D",
                    ...
                }
            }
            """
            string_id = [i for i in enode_content["children"] if "String" in i]
            if len(string_id) != 1:
                raise ValueError(
                    f"Invalid number of strings for var {id} ({len(string_id)})"
                )
            string_id = string_id[0]
            string_value = content[string_id]["op"].strip('"')
            return ENode(
                ENodeID(id),
                enode_content["op"],
                None,
                string_value,
                None,
                child_eclass_ids,
                enode_content["eclass"],
            )
        elif enode_content["op"][0:4] == "Bool":
            """Bool true should look like:
            {
                "function-A-Bool": {
                    "op": "Bool",
                    "children": ["bool-B"],
                    "eclass": "MLTL-E",
                    ...
                }
            }
            """
            bool_id = [i for i in enode_content["children"] if "bool" in i]
            if len(bool_id) != 1:
                raise ValueError(
                    f"Invalid number of bools for var {id} ({len(bool_id)})"
                )
            bool_id = bool_id[0]
            bool_value = True if content[bool_id]["op"].find("true") > -1 else False
            return ENode(
                ENodeID(id),
                enode_content["op"],
                None,
                None,
                bool_value,
                child_eclass_ids,
                enode_content["eclass"],
            )
        else:
            """Other operators should look like:
            {
                "function-A-Operator": {
                    "op": "Operator",
                    "children": ["function-B-Operand", "function-C-Operand"],
                    "eclass": "MLTL-F",
                    ...
                }
            }
            """
            return ENode(
                ENodeID(id),
                enode_content["op"],
                None,
                None,
                None,
                child_eclass_ids,
                enode_content["eclass"],
            )
    
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, ENode) and self.enode_id ==__value.enode_id
    
    def __hash__(self) -> int:
        return hash(self.enode_id)

    def __str__(self) -> str:
        s = f"{self.enode_id}: {self.op}"
        if self.interval is not None:
            s += f"[{self.interval[0]},{self.interval[1]}]"
        if self.value is not None:
            s += f" {self.value}"
        elif self.string is not None:
            s += f" {self.string}"
        else:
            s += f" {self.child_eclass_ids}"
        return s + f" ({self.eclass_id})"

def find_match(start: cpt.Expression, eclasses: dict[EClassID, set[ENode]], context: cpt.Context) -> Optional[ENode]:
    """Find the matching ENode for the given expression."""
    def enode_matches_expr(enode: ENode, expr: cpt.Expression) -> bool:
        nonlocal eclasses
        
        if isinstance(expr, cpt.Atomic):
            log.debug(5, f"{repr(expr)} : {enode.string} : atomic_id {context.atomic_id_map[expr]}")
        if isinstance(expr, cpt.Atomic) and enode.string == f"a{context.atomic_id_map[expr]}":
            log.debug(5, f"{enode.enode_id} matches expr {repr(expr)}")
            return True

        if any(
            [
                isinstance(expr, cpt.Constant) and enode.op != "Bool",
                cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE) and enode.op != "Not",
                cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND) and enode.op[0:3] != "And",
                cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR) and enode.op[0:2] != "Or",
                cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES) and enode.op != "Implies",
                cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV) and enode.op != "Equiv",
                cpt.is_operator(expr, cpt.OperatorKind.GLOBAL) and enode.op != "Global",
                cpt.is_operator(expr, cpt.OperatorKind.FUTURE) and enode.op != "Future",
                cpt.is_operator(expr, cpt.OperatorKind.UNTIL) and enode.op != "Until",
                cpt.is_operator(expr, cpt.OperatorKind.RELEASE) and enode.op != "Release",
            ]
        ):
            log.debug(5, f"{enode.enode_id} does not match expr {repr(expr)}")
            return False

        # Check that the interval matches
        if isinstance(expr, cpt.TemporalOperator):
            lb, ub = expr.interval.lb, expr.interval.ub
            if enode.interval is None:
                log.debug(5, f"{enode.enode_id} does not have an interval")
                return False
            if enode.interval[0] != lb or enode.interval[1] != ub:
                log.debug(5, f"{enode.enode_id} does not have the correct interval {lb, ub}")
                return False

        # Check that the children match
        relevant_child_eclasses = [
            c
            for c in enode.child_eclass_ids
            if "Interval" not in c
            and "String" not in c
            and "i64" not in c
            and "bool" not in c
        ]

        if len(relevant_child_eclasses) != len(expr.children):
            log.debug(5, f"{enode.enode_id} does not have the correct number of children {len(relevant_child_eclasses)} != {len(expr.children)}")
            return False

        for i in range(len(relevant_child_eclasses)):
            if not eclass_matches_expr(relevant_child_eclasses[i], expr.children[i]):
                log.debug(5, f"{enode.enode_id} does not have the correct child {repr(relevant_child_eclasses[i])} != {repr(expr.children[i])}")
                return False

        log.debug(5, f"{enode.enode_id} matches expr {repr(expr)}")
        return True

    def eclass_matches_expr(eclass: EClassID, expr: cpt.Expression) -> bool:
        nonlocal eclasses
        log.debug(5, f"Checking {eclass} against expr {repr(expr)}")
        return any(enode_matches_expr(enode, expr) for enode in eclasses[eclass])
        
    for eclass_id in eclasses:
        for enode in eclasses[eclass_id]:
            if enode_matches_expr(enode, start):
                return enode

    log.internal(f"no match found for {start}")
    return None

class EGraph:
    """An EGraph is a set of equivalence classes (EClasses) and a root ENode."""
    
    def __init__(self, eclasses: dict[EClassID, set[ENode]], root_enode: ENode, root_expr: cpt.Expression, context: cpt.Context):
        self.eclasses = eclasses
        self.root_enode = root_enode
        self.root_expr = root_expr
        self.gurobi_enode_vars_ = {}
        self.gurobi_eclass_vars_ = {}
        self.context = context
        self.enodes = { n for n in eclasses.values() for n in n }
        self.enode_wpds: dict[ENode, int] = { n: 0 for n in self.enodes }
        self.eclass_wpds: dict[EClassID, int] = { c: 0 for c in eclasses.keys() }
        self.enode_bpds: dict[ENode, int] = { n: 0 for n in self.enodes }
        self.eclass_bpds: dict[EClassID, int] = { c: 0 for c in eclasses.keys() }

    @staticmethod
    def from_json(content: dict[str, dict], start: cpt.Expression, context: cpt.Context) -> Optional[EGraph]:
        """Return an `EClass` from egglog-generated JSON. Content should the "nodes" key of the JSON."""
        eclasses: dict[EClassID, set[ENode]] = {}

        for enode_id in content:
            # Skip interval, string, and boolean nodes
            if "Interval" in enode_id or "String" in enode_id or "i64" in enode_id or "bool" in enode_id:
                continue

            enode = ENode.from_json(enode_id, content)

            if enode.eclass_id not in eclasses:
                eclasses[enode.eclass_id] = set()
            eclasses[enode.eclass_id].add(enode)

        root_enode = find_match(start, eclasses, context)
        if root_enode is None:
            return None
        egraph = EGraph(eclasses, root_enode, start, context)

        # Remove all cycles of length 2 or less
        # This is sound since our rewrites only introduce cycles of at most 2
        # One such rewrite is !!p |-> p        
        log.debug(2, "removing cycles from egraph")
        start_time = util.get_rusage_time()
        for enode in egraph.enodes:
            if egraph.has_cycle(enode, 2) and len(egraph.eclasses[enode.eclass_id]) > 1:
                log.debug(3, f"Removing cycle from {enode}")
                egraph.eclasses[enode.eclass_id].remove(enode)
        egraph.context.stats.eqsat_cycle_removal_time = util.get_rusage_time() - start_time

        return egraph

    def has_cycle(self, enode: ENode, max_loop_len: int) -> bool:
        """Returns True if the EGraph has a cycle up to length i starting from the given ENode."""
        def get_children(enode: ENode, i: int) -> set[EClassID]:
            """ 
            Returns the children of the given ENode at depth i.
            i=1 means immediate children, i=2 means children of children, etc.
            """
            if i == 0:
                return set()
                
            # Stack with elements (EClassID, depth)
            stack: list[tuple[EClassID, int]] = [(c, 0) for c in enode.child_eclass_ids]
            # log.debug(5, f"Initial stack: {stack}")
            result: set[EClassID] = set()
            while len(stack) > 0:
                cur, depth = stack.pop()
                # log.debug(5, f"Popped: {cur}, {depth}")
                if depth == i:
                    result.add(cur)
                    # log.debug(5, f"Added {cur} to result at depth {depth}")
                    continue
                for enode in self.eclasses[cur]:
                    for child_eclass_id in enode.child_eclass_ids:
                        # log.debug(5, f"Pushing {child_eclass_id} at depth {depth + 1}")
                        stack.append((child_eclass_id, depth + 1))

            return result

        # log.debug(5, "-"*100)
        # log.debug(5, f"Computing children of {enode} at depth {max_loop_len}")
        # log.debug(5, "")

        for i in range(max_loop_len):
            result = get_children(enode, i)
            if enode.eclass_id in result:
                # log.debug(5, "")
                # log.debug(5, f"Children of {enode} at depth {max_loop_len}: {result}")
                # log.debug(5, f"{result}")
                # log.debug(5, "CYCLE FOUND\n" if enode.eclass_id in result else "")
                return True

        return False

    def get_children(self, enode: ENode) -> list[EClassID]:
        return enode.child_eclass_ids

    def get_parents(self, enode: ENode) -> list[ENode]:
        parents = []
        for enode_ in self.enodes:
            if enode.eclass_id in enode_.child_eclass_ids:
                parents.append(enode_)
        return parents

    def get_siblings_with_parent(self, enode: ENode) -> set[tuple[EClassID, ENode]]:
        siblings_with_parent = set()
        for parent in self.get_parents(enode):
            for sibling_eclass_id in [c for c in parent.child_eclass_ids if c != enode.eclass_id]:
                siblings_with_parent.add((sibling_eclass_id, parent))
        return siblings_with_parent

    def build_gurobi_model_(self, env: gp.Env, timeout: int) -> gp.Model:
        """Returns a Gurobi model representing the EGraph."""
        start_time = util.get_rusage_time()
        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(timeout)

        model = gp.Model("EGraph", env=env)
        # model.setParam("OutputFlag", 0)

        eclass_vars: dict[EClassID, gp.Var] = {}
        enode_vars: dict[ENode, gp.Var] = {}
        wpd_vars: dict[ENode, gp.Var] = {}
        bpd_vars: dict[ENode, gp.Var] = {}
        wpd_active_vars: dict[ENode, gp.Var] = {}
        wpd_active_siblings_vars: dict[ENode, dict[ENode, dict[ENode, gp.Var]]] = {}
        max_sib_wpd_vars: dict[ENode, gp.Var] = {}
        wpb_bpd_diff_vars: dict[ENode, gp.Var] = {}
        cost_vars: dict[ENode, gp.Var] = {}
        cost_active_vars: dict[ENode, gp.Var] = {}

        for eclass_id in self.eclasses.keys():
            eclass_vars[eclass_id] = model.addVar(vtype=GRB.BINARY, name=f"eclass({eclass_id})")

        for enode in self.enodes:
            enode_vars[enode] = model.addVar(vtype=GRB.BINARY, name=f"enode({enode.enode_id})")
            wpd_vars[enode] = model.addVar(vtype=GRB.INTEGER, name=f"wpd({enode.enode_id})")
            bpd_vars[enode] = model.addVar(vtype=GRB.INTEGER, name=f"bpd({enode.enode_id})")
            wpd_active_vars[enode] = model.addVar(vtype=GRB.INTEGER, name=f"wpd_active({enode.enode_id})")

            wpd_active_siblings_vars[enode] = {}
            for sibling_enode, parent_enode in [
                (sibling_enode, parent_enode)
                for sibling_eclass_id, parent_enode in self.get_siblings_with_parent(
                    enode
                )
                for sibling_enode in self.eclasses[sibling_eclass_id]
            ]:
                if parent_enode not in wpd_active_siblings_vars[enode]:
                    wpd_active_siblings_vars[enode][parent_enode] = {}
                wpd_active_siblings_vars[enode][parent_enode][sibling_enode] = (
                    model.addVar(
                        vtype=GRB.INTEGER,
                        name=f"wpd_active_sibling({enode.enode_id},{parent_enode.enode_id},{sibling_enode.enode_id})",
                    )
                )

            max_sib_wpd_vars[enode] = model.addVar(vtype=GRB.INTEGER, name=f"max_sib_wpd({enode.enode_id})")
            wpb_bpd_diff_vars[enode] = model.addVar(lb=(- self.root_expr.wpd), vtype=GRB.INTEGER, name=f"wpb_bpd_diff({enode.enode_id})")
            cost_vars[enode] = model.addVar(vtype=GRB.INTEGER, name=f"cost({enode.enode_id})")
            cost_active_vars[enode] = model.addVar(vtype=GRB.INTEGER, name=f"cost_active({enode.enode_id})")

        model.addConstr(
            eclass_vars[self.root_enode.eclass_id] == 1,
            name="root_eclass"
        )
        
        # For each enode n, if n=1 then all of n's children must be 1
        # n * len(children(n)) == n * sum(children(n))
        for enode in self.enodes:
            var = enode_vars[enode]
            child_sum = gp.quicksum(eclass_vars[child] for child in self.get_children(enode))
            len_child = len(enode.child_eclass_ids)
            model.addConstr((var * len_child) == (var * child_sum), f"n_{enode.enode_id}_children_constr")

        # For each eclass c, if c=1 then n=1 for at least one of the nodes n in c
        # c <= sum(nodes(c))
        for eclass_id in self.eclasses:
            eclass_var = eclass_vars[eclass_id]
            nodes_sum = gp.quicksum(enode_vars[enode] for enode in self.eclasses[eclass_id])
            model.addConstr(eclass_var <= nodes_sum)

        for enode in self.enodes:
            wpd_var = wpd_vars[enode]
            bpd_var = bpd_vars[enode]
            if enode.op == "Var":
                model.addConstr(wpd_var == 0)
                model.addConstr(bpd_var == 0)
            elif enode.interval is None:
                model.addConstr(
                    wpd_var == gp.max_(
                        *[wpd_vars[n] for c in enode.child_eclass_ids for n in self.eclasses[c]],
                        constant=0
                    ),
                )
                model.addConstr(
                    bpd_var == gp.min_(
                        *[bpd_vars[n] for c in enode.child_eclass_ids for n in self.eclasses[c]],
                        constant=self.root_expr.bpd
                    ),
                )
            else:
                tmp_wpd_var = model.addVar(vtype=GRB.INTEGER, name=f"wpd_tmp_{enode.enode_id}")
                tmp_bpd_var = model.addVar(vtype=GRB.INTEGER, name=f"bpd_tmp_{enode.enode_id}")
                model.addConstr(
                    tmp_wpd_var == gp.max_(
                        *[wpd_vars[n] for c in enode.child_eclass_ids for n in self.eclasses[c]],
                        constant=0
                    ),
                    f"tmp_wpd_var_constr_{enode.enode_id}"
                )
                model.addConstr(wpd_var == tmp_wpd_var + enode.interval[1])
                model.addConstr(
                    tmp_bpd_var == gp.min_(
                        *[bpd_vars[n] for c in enode.child_eclass_ids for n in self.eclasses[c]],
                        constant=self.root_expr.bpd
                    ),
                    f"tmp_bpd_var_constr_{enode.enode_id}"
                )
                model.addConstr(bpd_var == tmp_bpd_var + enode.interval[0])

        for enode in self.enodes:
            wpd_active_var = wpd_active_vars[enode]
            max_sib_wpd_var = max_sib_wpd_vars[enode]
            wpb_bpd_diff_var = wpb_bpd_diff_vars[enode]
            cost_var = cost_vars[enode]
            cost_active_var = cost_active_vars[enode]

            model.addConstr(wpd_active_var == enode_vars[enode] * wpd_vars[enode])

            # Siblings are only counted if their shared parent is active
            for sibling_enode, parent_enode in [
                (sibling_enode, parent_enode)
                for sibling_eclass_id, parent_enode in self.get_siblings_with_parent(
                    enode
                )
                for sibling_enode in self.eclasses[sibling_eclass_id]
            ]:
                model.addConstr(
                    wpd_active_siblings_vars[enode][parent_enode][sibling_enode]
                    == enode_vars[parent_enode] * wpd_active_vars[sibling_enode]
                )

            model.addConstr(max_sib_wpd_var == gp.max_(
                    *[
                        wpd_active_siblings_vars[enode][parent_enode][sibling_enode] 
                        for sibling_eclass_id, parent_enode in self.get_siblings_with_parent(
                            enode
                        )
                        for sibling_enode in self.eclasses[sibling_eclass_id]
                    ],
                    constant=0
                ),
            )

            model.addConstr(wpb_bpd_diff_var == (max_sib_wpd_var - bpd_vars[enode]))
            model.addConstr(cost_var == gp.max_(wpb_bpd_diff_var, constant=0))
            model.addConstr(cost_active_var == enode_vars[enode] * (cost_var + 1))

        model.setObjective(gp.quicksum(cost_active_vars[enode] for enode in self.enodes), GRB.MINIMIZE)
        signal.alarm(0) # Disable the alarm

        self.gurobi_enode_vars_ = enode_vars
        self.gurobi_eclass_vars_ = eclass_vars

        self.context.stats.eqsat_gurobi_encoding_time = util.get_rusage_time() - start_time

        return model

    def build_repr_map_(self) -> dict[EClassID, ENode]:
        log.debug(2, "building repr map")

        repr_map: dict[EClassID, ENode] = {}
        for eclass_id in [c for c in self.eclasses if self.gurobi_eclass_vars_[c].X == 1]:
            enode = next(enode for enode in self.eclasses[eclass_id] if self.gurobi_enode_vars_[enode].X == 1)
            repr_map[eclass_id] = enode

        log.debug(3, "repr_map:")
        log.debug(3, pprint.pformat(repr_map))

        return repr_map

    def build_expr_(self, repr_map: dict[EClassID, ENode]) -> cpt.Expression:
        """
        Converts the Gurobi variables to a CPT Expression.
        """
        log.debug(2, "building expr")

        def build_expr_recur(enode: ENode) -> cpt.Expression:
            if enode.op == "Bool":
                return cpt.Constant(log.EMPTY_FILE_LOC, True)
            elif enode.op == "Var":
                if not enode.string:
                    raise ValueError("No string for Var")
                expr = next(e for e,i in self.context.atomic_id_map.items() if i == int(enode.string.replace('"','')[1:]))
                expr.parents.clear()
                return expr
            elif enode.op == "Not":
                return cpt.Operator.LogicalNegate(log.EMPTY_FILE_LOC, build_expr_recur(repr_map[enode.child_eclass_ids[0]]))
            elif enode.op[0:3] == "And":
                return cpt.Operator.LogicalAnd(log.EMPTY_FILE_LOC, [build_expr_recur(repr_map[c]) for c in enode.child_eclass_ids])
            elif enode.op[0:2] == "Or":
                return cpt.Operator.LogicalOr(log.EMPTY_FILE_LOC, [build_expr_recur(repr_map[c]) for c in enode.child_eclass_ids])
            elif enode.op == "Equiv":
                return cpt.Operator.LogicalIff(log.EMPTY_FILE_LOC, build_expr_recur(repr_map[enode.child_eclass_ids[0]]), build_expr_recur(repr_map[enode.child_eclass_ids[1]]))
            elif enode.op == "Implies":
                return cpt.Operator.LogicalImplies(log.EMPTY_FILE_LOC, build_expr_recur(repr_map[enode.child_eclass_ids[0]]), build_expr_recur(repr_map[enode.child_eclass_ids[1]]))
            elif enode.op == "Global" and enode.interval is not None:
                return cpt.TemporalOperator.Global(log.EMPTY_FILE_LOC, enode.interval[0], enode.interval[1], build_expr_recur(repr_map[enode.child_eclass_ids[0]]))
            elif enode.op == "Future" and enode.interval is not None:
                return cpt.TemporalOperator.Future(log.EMPTY_FILE_LOC, enode.interval[0], enode.interval[1], build_expr_recur(repr_map[enode.child_eclass_ids[0]]))
            elif enode.op == "Until" and enode.interval is not None:
                return cpt.TemporalOperator.Until(log.EMPTY_FILE_LOC, enode.interval[0], enode.interval[1], build_expr_recur(repr_map[enode.child_eclass_ids[0]]), build_expr_recur(repr_map[enode.child_eclass_ids[1]]))
            elif enode.op == "Release" and enode.interval is not None:
                return cpt.TemporalOperator.Release(log.EMPTY_FILE_LOC, enode.interval[0], enode.interval[1], build_expr_recur(repr_map[enode.child_eclass_ids[0]]), build_expr_recur(repr_map[enode.child_eclass_ids[1]]))
            else:
                raise ValueError(f"Invalid node type {enode.op}")

        return build_expr_recur(repr_map[self.root_enode.eclass_id])

    def extract(self, max_time: float, max_memory: int) -> Optional[cpt.Expression]:
        """
        Extracts an optimal expression from the EGraph using Gurobi optimizer.
        """
        with gp.Env(empty=True) as env:
            env.setParam('OutputFlag', 0)
            if max_time > 0:
                env.setParam('TimeLimit', max_time)
            if max_memory > 0:
                env.setParam('SoftMemLimit', max_memory)
            env.start()

            try:
                model = self.build_gurobi_model_(env, int(max_time))
            except TimeoutError:
                log.warning(f"gurobi encoding timed out after {max_time} seconds")
                self.context.stats.eqsat_gurobi_solver_status = "encoding_timeout"
                self.context.stats.eqsat_gurobi_solver_time = -1.0
                return None

            start_time = util.get_rusage_time()
            log.debug(2, "optimizing gurobi model")
            try:
                model.optimize()
            except Exception as e:
                if "Model too large for size-limited license" in str(e):
                    log.error("gurobi model too large for size-limited license; see https://gurobi.com/unrestricted for more information")
                    self.context.stats.eqsat_gurobi_solver_status = "bad_license"
                    self.context.stats.eqsat_gurobi_solver_time = -1.0
                    return None
                log.internal(f"gurobi optimization failed: {e}")
                self.context.stats.eqsat_gurobi_solver_status = "failure"
                self.context.stats.eqsat_gurobi_solver_time = -1.0
                return None

            self.context.stats.eqsat_gurobi_solver_time = util.get_rusage_time() - start_time
            self.context.stats.eqsat_gurobi_solver_status = "ok"

            if model.status == GRB.INFEASIBLE:
                iis_path = pathlib.Path("model.ilp")
                log.internal(
                    f"gurobi model is infeasible, computing IIS and saving to {iis_path}\n"
                     "    this may take some time..."
                )
                model.computeIIS()
                model.write(str(iis_path))
                self.context.stats.eqsat_gurobi_solver_status = "infeasible"
                return None
            elif model.status == GRB.TIME_LIMIT:
                log.warning(f"gurobi timed out after {max_time} seconds")
                self.context.stats.eqsat_gurobi_solver_status = "timeout"
                self.context.stats.eqsat_gurobi_solver_time = -1.0
                return None
            elif model.status == GRB.MEM_LIMIT:
                log.warning(f"gurobi ran out of memory after {max_memory} MB")
                self.context.stats.eqsat_gurobi_solver_status = "mem_limit"
                return None
            elif model.status != GRB.OPTIMAL:
                log.internal(f"gurobi failed with status {model.status}")
                self.context.stats.eqsat_gurobi_solver_status = "failure"
                return None

            log.debug(3, "Gurobi variables:")
            for v in sorted(model.getVars(), key=lambda x: x.VarName):
                log.debug(3, f"  {v.VarName:33} {v.X:g}")
            log.debug(3, f"Minimum cost: {model.ObjVal:g}")

            log.debug(3, f"num enodes active: {sum(1 for enode in self.enodes if self.gurobi_enode_vars_[enode].X == 1)}")
            log.debug(3, f"enodes active: {[enode.enode_id for enode in self.enodes if self.gurobi_enode_vars_[enode].X == 1]}")

        repr_map = self.build_repr_map_()
        return self.build_expr_(repr_map)

    def print(self) -> None:
        """Prints a string representation of the entire EGraph."""
        print(f"Root: {self.root_enode}")
        for eclass_id, enodes in sorted(self.eclasses.items()):
            print(f"EClass({eclass_id}):")
            for enode in sorted(enodes, key=lambda x: x.enode_id):
                print(f"  {enode}")
