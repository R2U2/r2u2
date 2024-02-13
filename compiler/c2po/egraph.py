"""Module for computing the optimal equivalent expression with respect to SCQ sizing.

We use `egglog` to perform equality saturation and do the extraction of the optimal expression ourselves (due to the complex nature of SCQ sizing). `egglog` does automatic extraction, but works best for cases where the cost of each node can be easily computed using just the children of a given node.
"""
from __future__ import annotations
import subprocess
import pathlib
import dataclasses
import json
from typing import Optional, NewType, cast

from c2po import cpt, log, types

MODULE_CODE = "EGRF"

INF = 1_000_000_000

FILE_DIR = pathlib.Path(__file__).parent

EGGLOG_PATH = FILE_DIR / "egglog" / "target" / "debug" / "egglog"
PRELUDE_PATH = FILE_DIR / "mltl.egg"

TMP_EGG_PATH = FILE_DIR / "__tmp__.egg"
EGGLOG_OUTPUT = TMP_EGG_PATH.with_suffix(".json")

PRELUDE_END = "(run-schedule (saturate mltl-rewrites))"

ENodeID = NewType('ENodeID', str)
EClassID = NewType('EClassID', str)

@dataclasses.dataclass
class ENode:
    enode_id: ENodeID
    op: str
    interval: Optional[types.Interval]
    string: Optional[str]
    child_eclass_ids: list[EClassID]
    eclass_id: EClassID

    @staticmethod
    def from_json(id: str, content: dict) -> ENode:
        """Return an `ENode` from egglog-generated JSON, integrating Interval data into a temporal operators ENode."""
        enode_content = content[id]
        child_eclass_ids = [content[c]["eclass"] for c in enode_content["children"] if "Interval" not in c and "String" not in c]

        if enode_content["op"] in {"Global", "Future", "Until", "Release"}:
            # Temporal op "G[4,10] (...)" should look like:
            # "Global-abc":   {"op"="Global","children"=["Interval-def","..."],...}
            # "Interval-def": {"op"="Interval","children"=["i64-ghi","i64-jkl"],...}
            # 'i64-ghi':      {"op"=4,...}
            # 'i64-jkl':      {"op"=10,...}
            interval_id = [i for i in enode_content["children"] if "Interval" in i]

            if len(interval_id) != 1:
                raise ValueError(f"Invalid number of intervals for temporal op {id} ({len(interval_id)})")
            
            interval_id = interval_id[0]
            interval_content = content[interval_id]

            if len(interval_content["children"]) != 2:
                raise ValueError(f"Invalid number of children for interval {interval_id} ({len(interval_content['children'])})")
            
            lb_id = interval_content["children"][0]
            ub_id = interval_content["children"][1]

            lb = int(content[lb_id]["op"])
            ub = int(content[ub_id]["op"])

            return ENode(ENodeID(id), enode_content["op"], types.Interval(lb,ub), None, child_eclass_ids, enode_content["eclass"])
        elif enode_content["op"][0:3] == "Var":
            # Var "a0" should look like:
            # "Var-abc":   {"op"="Var","children"=["String-def"],...}
            # "String-def": {"op"="a0",...}
            string_id = [i for i in enode_content["children"] if "String" in i]

            if len(string_id) != 1:
                raise ValueError(f"Invalid number of strings for var {id} ({len(string_id)})")
            
            string_id = string_id[0]
            string_value = content[string_id]["op"]
            
            return ENode(ENodeID(id), enode_content["op"], None, string_value, child_eclass_ids, enode_content["eclass"])
        else:
            return ENode(ENodeID(id), enode_content["op"], None, None, child_eclass_ids, enode_content["eclass"])
    
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, ENode) and self.enode_id ==__value.enode_id
    
    def __hash__(self) -> int:
        return hash(self.enode_id)


@dataclasses.dataclass
class EGraph:
    """Class representing a saturated EGraph for an expression."""
    root: EClassID
    eclasses: dict[EClassID, set[ENode]]

    @staticmethod
    def empty() -> EGraph:
        return EGraph(EClassID(""), {})

    @staticmethod
    def from_json(content: dict) -> EGraph:
        """Construct a new `EGraph` from a dict representing the JSON output by `egglog`."""
        eclasses: dict[EClassID, set[ENode]] = {}

        for enode_id,_ in content["nodes"].items():
            # do not add intervals nor i64s to the EGraph
            if "Interval" in enode_id or "i64" in enode_id or "String" in enode_id:
                continue

            enode = ENode.from_json(enode_id, content["nodes"])

            # If this is a temporal op with interval [0,0] then it's redundant, so don't add it
            if enode.interval and enode.interval.lb == 0 and enode.interval.ub == 0:
                continue

            if enode.eclass_id not in eclasses:
                eclasses[enode.eclass_id] = {enode}
            else:
                eclasses[enode.eclass_id].add(enode)

        if len(eclasses) < 1:
            log.error("Empty EGraph", MODULE_CODE)
            return EGraph(EClassID(""),{})
        
        parents: dict[str, set[str]] = {i:set() for i in eclasses.keys()}

        for eclass_id,nodes in eclasses.items():
            for enode in nodes:
                for child_eclass_id in enode.child_eclass_ids:
                    parents[child_eclass_id].add(eclass_id)

        root_candidates = [id for id,pars in parents.items() if len(pars) == 0]

        if len(root_candidates) == 1:
            return EGraph(EClassID(root_candidates[0]), eclasses)
        elif len(root_candidates) > 1:
            raise ValueError(f"Many root candidates -- possible self-loop back to true root node {root_candidates}")
        else:
            raise ValueError("No root candidates")
    
    def traverse(self):
        stack: list[ENode] = []
        visited = set()

        [stack.append(enode) for enode in self.eclasses[self.root]]

        while len(stack) > 0:
            cur_enode = stack.pop()

            if cur_enode.enode_id in visited:
                yield cur_enode
                continue

            stack.append(cur_enode)
            visited.add(cur_enode.enode_id)

            for enode in self.eclasses[cur_enode.eclass_id]:
                for child_eclass_id in enode.child_eclass_ids:
                    if child_eclass_id in visited:
                        continue

                    [stack.append(child) for child in self.eclasses[child_eclass_id]]

    def compute_propagation_delays(self) -> tuple[dict[EClassID, int], dict[EClassID, int]]:
        """Returns a pair of dicts mapping EClass IDs to propagation delays (PDs). The first dict maps to the maximum best-case PD (BPD) of the EClass and the second maps to the minimum worst-case PD (WPD).
         
        For minimizing cost, it's best for BPD to be high and WPD to be low. While two ENodes in the same EClass can have different PDs, one ENode will always have the "best" PDs. The only case when two nodes will differ is due to temporal vacuity:

            `(G[0,10] a) | (G[2,5] a) ==> G[2,5] a`

            `(F[0,10] a) & (F[2,5] a) ==> F[2,5] a`

        where one formula always implies the other in a conjunction/disjunction. The PDs of the removed operator are always inclusive of the kept operator (i.e., [2,5] is in [0,10]), so the BPD is higher and WPD is lower for the kept operator. This will always result in lower memory encoding due to the SCQ sizing formula relying on a subtraction of BPD and addition of sibling WPD.

        TODO: what to do about nodes that do not share optimal PD?
        """
        max_bpd: dict[EClassID, int] = {s:0  for s in self.eclasses.keys()}
        min_wpd: dict[EClassID, int] = {s:INF for s in self.eclasses.keys()}

        for enode in self.traverse():
            if enode.op[0:3] == "Var":
                max_bpd[enode.eclass_id] = 0
                min_wpd[enode.eclass_id] = 0
            elif enode.op[0:3] == "And":
                cur_bpd = min([max_bpd[i] for i in enode.child_eclass_ids])

                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) == 0:
                    cur_wpd = INF
                else:
                    cur_wpd = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF])

                max_bpd[enode.eclass_id] = max(max_bpd[enode.eclass_id], cur_bpd)
                min_wpd[enode.eclass_id] = min(min_wpd[enode.eclass_id], cur_wpd)
            elif enode.op == "Global":
                interval = enode.interval
                if not interval:
                    raise ValueError("No 'Interval' for 'Global' operator")

                cur_bpd = min([max_bpd[i] for i in enode.child_eclass_ids]) + interval.lb
                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) == 0:
                    cur_wpd = INF
                else:
                    cur_wpd = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) + interval.ub

                max_bpd[enode.eclass_id] = max(max_bpd[enode.eclass_id], cur_bpd)
                min_wpd[enode.eclass_id] = min(min_wpd[enode.eclass_id], cur_wpd)

        return (max_bpd, min_wpd)

    def compute_cost(self) -> dict[ENodeID, int]:
        """Compute the cost of each ENode in this EGraph. The cost of an ENode is the sum of the SCQ sizes of each of its children.

        Consider the following EGraph (where each EClass has a single ENode in it):
 
            op0         op1
            |           |
        ____|______  ___|___
        |         |  |     |
        v         v  v     v
        phi0      phi1     phi2
        (wpd=10)  (wpd=1)  (wpd=5)

        To compute the cost of phi1, we see that phi0 and ph1 are siblings, as are phi1 and phi2, but wouldn't recognize this from traversing op0 and op1 separately. So, we compute each nodes' max sibling WPD as a separate pass.
        
        If op0 is not in the extracted expression, then the SCQ size of phi1 will be 5. 
        But if it IS in the extracted expression. then the SCQ size of phi1 will be 10.
        The cost of each ENode is the sum of the SCQ sizes of its children. 
        """
        cost: dict[ENodeID, int] = {s.enode_id:INF  for s in self.traverse()}

        max_bpd, min_wpd = self.compute_propagation_delays()

        # Compute cost of each ENode
        for enode in self.traverse():
            if enode.op[0:3] == "Var":
                # no children, so 0
                cost[enode.enode_id] = 1
            elif enode.op[0:3] == "And":
                total_scq_size = 0

                # need max wpd of all children and second max wpd (for the node with the max wpd)
                cur_max_wpd_1 = max([min_wpd[i] for i in enode.child_eclass_ids])

                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] != cur_max_wpd_1]) == 0:
                    cur_max_wpd_2 = cur_max_wpd_1
                else:
                    cur_max_wpd_2 = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] != cur_max_wpd_1])

                for child_eclass_id in enode.child_eclass_ids:
                    if min_wpd[child_eclass_id] == cur_max_wpd_1:
                        total_scq_size += max(cur_max_wpd_2 - max_bpd[child_eclass_id], 0) + 1
                    else:
                        total_scq_size += max(cur_max_wpd_1 - max_bpd[child_eclass_id], 0) + 1

                cost[enode.enode_id] = total_scq_size
            elif enode.op == "Global":
                # Global nodes have *lonely* single children (no siblings)
                cost[enode.enode_id] = 1

        return cost

    def extract(self, context: cpt.Context) -> cpt.Expression:
        rep: dict[EClassID, tuple[ENode, int]] = {}

        cost: dict[ENodeID, int] = self.compute_cost()

        # TODO: can the rep for an EClass change after one of its parents' rep has been computed?
        for enode in self.traverse():
            total_cost = sum([cost[rep[c][0].enode_id] for c in enode.child_eclass_ids]) + cost[enode.enode_id]

            if enode.eclass_id not in rep or total_cost < rep[enode.eclass_id][1]:
                rep[enode.eclass_id] = (enode, total_cost)

        def build_expr_tree(eclass: EClassID) -> cpt.Expression:
            enode,_ = rep[eclass]

            if enode.op[0:3] == "Var":
                if not enode.string:
                    raise ValueError("No string for Var")
                # TODO: map these back to their expressions using context.atomics
                return cpt.Variable(log.EMPTY_FILE_LOC, enode.string.replace("\"",""))
            elif enode.op[0:3] == "And":
                ch = [build_expr_tree(c) for c in enode.child_eclass_ids]
                return cpt.Operator.LogicalAnd(log.EMPTY_FILE_LOC, ch)
            elif enode.op == "Global":
                ch = [build_expr_tree(c) for c in enode.child_eclass_ids]
                ch = ch[0]
                if not enode.interval:
                    raise ValueError("No Interval for Global")
                return cpt.TemporalOperator.Global(log.EMPTY_FILE_LOC, enode.interval.lb, enode.interval.ub, ch)
            elif enode.op == "Future":
                ch = [build_expr_tree(c) for c in enode.child_eclass_ids]
                ch = ch[0]
                if not enode.interval:
                    raise ValueError("No Interval for Future")
                return cpt.TemporalOperator.Future(log.EMPTY_FILE_LOC, enode.interval.lb, enode.interval.ub, ch)
            elif enode.op == "Until":
                ch = [build_expr_tree(c) for c in enode.child_eclass_ids]
                ch0 = ch[0]
                ch1 = ch[1]
                if not enode.interval:
                    raise ValueError("No Interval for Until")
                return cpt.TemporalOperator.Until(log.EMPTY_FILE_LOC, enode.interval.lb, enode.interval.ub, ch0 ,ch1)

            raise ValueError(f"Invalid node type ({enode.op})")

        expr_tree = build_expr_tree(self.root)

        print(repr(expr_tree))
        print(rep[self.root][1])

        return expr_tree


def to_egglog(spec: cpt.Formula) -> str:
    """Returns a string that represents `spec` in egglog syntax."""
    egglog = f"(let {spec.symbol[1:] if spec.symbol[0] == '#' else spec.symbol} "

    stack: list["tuple[int, cpt.Expression]"] = []
    stack.append((0, spec.get_expr()))

    while len(stack) > 0:
        (seen, expr) = stack.pop()

        if isinstance(expr, cpt.Constant):
            egglog += expr.symbol
        elif expr.atomic_id > -1:
            egglog += f"(Var \"a{expr.atomic_id}\")"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            if seen == 0:
                egglog += "(Not ("
                stack.append((seen+1, expr))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            if seen == 0:
                egglog += f"(Global (Interval {expr.interval.lb} {expr.interval.ub}) "
                stack.append((seen+1, expr))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            if seen == 0:
                egglog += f"(Future (Interval {expr.interval.lb} {expr.interval.ub}) "
                stack.append((seen+1, expr))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            if seen == 0:
                egglog += f"(Until (Interval {expr.interval.lb} {expr.interval.ub}) "
                stack.append((seen+1, expr))
                stack.append((0, expr.children[1]))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error("Release not implemented", MODULE_CODE)
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            arity = len(expr.children)
            if seen == 0:
                egglog += f"(And{arity} "
                stack.append((seen+1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                egglog += ")"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            arity = len(expr.children)
            if seen == 0:
                egglog += f"(Or{arity} "
                stack.append((seen+1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                egglog += ")"

    return egglog + ")\n"


def run_egglog(spec: cpt.Formula) -> EGraph:
    with open(PRELUDE_PATH, "r") as f:
        prelude = f.read()
    
    egglog = prelude + to_egglog(spec) + PRELUDE_END

    with open(TMP_EGG_PATH, "w") as f:
        f.write(egglog)

    command = [str(EGGLOG_PATH), "--to-json", str(TMP_EGG_PATH)]
    proc = subprocess.run(command, capture_output=True)

    if proc.returncode:
        log.error(f"Error running egglog\n{proc.stderr.decode()}", MODULE_CODE)
        return EGraph.empty()

    with open(EGGLOG_OUTPUT, "r") as f:
        egglog_output = json.load(f)

    egraph = EGraph.from_json(egglog_output)

    return egraph
