"""Module for computing the optimal equivalent expression with respect to SCQ sizing.

We use `egglog` to perform equality saturation and do the extraction of the optimal expression ourselves (due to the complex nature of SCQ sizing). `egglog` does automatic extraction, but works best for cases where the cost of each node can be easily computed using just the children of a given node.

`None` represents infinity for an `Optional[int]`.
"""
from __future__ import annotations
import subprocess
import pathlib
import dataclasses
import json
import pprint
from typing import Optional

from c2po import cpt, log, types

MODULE_CODE = "EGRF"

INF = 1_000_000_000

FILE_DIR = pathlib.Path(__file__).parent

EGGLOG_PATH = FILE_DIR / "egglog" / "target" / "debug" / "egglog"
PRELUDE_PATH = FILE_DIR / "mltl.egg"

TMP_EGG_PATH = FILE_DIR / "__tmp__.egg"
EGGLOG_OUTPUT = TMP_EGG_PATH.with_suffix(".json")

PRELUDE_END = "(run-schedule (saturate mltl-rewrites))"

@dataclasses.dataclass
class ENode:
    enode_id: str
    op: str
    child_eclass_ids: list[str] # child EClasses
    eclass_id: str

    @staticmethod
    def from_json(id: str, content: dict) -> ENode:
        return ENode(id, content["op"], content["children"], content["eclass"])
    
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, ENode) and self.enode_id ==__value.enode_id
    
    def __hash__(self) -> int:
        return hash(self.enode_id)
    
    def get_interval(self, eclasses: dict[str, set[ENode]]) -> Optional[types.Interval]:
        for child_id in self.child_eclass_ids:
            enodes = eclasses[child_id]

            # intervals should only be singletons
            if len(enodes) != 1:
                continue
            
            interval = enodes.copy().pop()
            if interval.op != "Interval":
                continue
            
            # Interval should look like (with lb=4, ub=10):
            # 'Interval-abcd': {ENode(id='...'), op='Interval', children=['i64-a', 'i64-b']}
            # 'i64-a': {ENode(id='...', op='4')}
            # 'i64-b': {ENode(id='...', op='10')}
            lb = int(eclasses[interval.child_eclass_ids[0]].copy().pop().op)
            ub = int(eclasses[interval.child_eclass_ids[1]].copy().pop().op)

            # lb = int(cast(ENode, eclasses[interval.children[0]]).op)
            # ub = int(cast(ENode, eclasses[interval.children[1]]).op)

            return types.Interval(lb, ub)
        
        # otherwise no children, no interval
        return None


@dataclasses.dataclass
class EGraph:
    root: str
    eclasses: dict[str, set[ENode]]

    @staticmethod
    def from_json(content: dict) -> EGraph:
        """Construct a new `EGraph` from a dict representing the JSON output by `egglog`."""
        eclass_ids: dict[str, str] = {}
        eclasses: dict[str, set[ENode]] = {}

        for enode_id,node in content["nodes"].items():
            eclass_ids[enode_id] = node["eclass"]

        for enode_id,node in content["nodes"].items():
            node["children"] = [eclass_ids[s] for s in node["children"]]
            enode = ENode.from_json(enode_id, node)

            # pprint.pprint(node)

            if enode.eclass_id not in eclasses:
                eclasses[enode.eclass_id] = {enode}
            else:
                eclasses[enode.eclass_id].add(enode)
            
            # pprint.pprint(eclasses[enode.eclass_id])
            # print("--------")

        if len(eclasses) < 1:
            log.error("Empty EGraph", MODULE_CODE)
            return EGraph("",{})
        
        parents: dict[str, set[str]] = {i:set() for i in eclasses.keys()}

        for eid,nodes in eclasses.items():
            for enode in nodes:
                for child_eclass_id in enode.child_eclass_ids:
                    parents[child_eclass_id].add(eid)

        root_candidates = [id for id,pars in parents.items() if len(pars) == 0]

        if len(root_candidates) == 1:
            egraph = EGraph(root_candidates[0], eclasses)
            # pprint.pprint(egraph.eclasses)
            return egraph
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

            stack.append(cur_enode) # FIXME: is this necessary?
            visited.add(cur_enode.enode_id)

            for enode in self.eclasses[cur_enode.eclass_id]:
                for child_eclass_id in [c for c in enode.child_eclass_ids if c not in visited]:
                    [stack.append(child) for child in self.eclasses[child_eclass_id]]

    def compute_reprs(self) -> dict[str, str]:
        """Compute the representative E-Node for each E-class in `self`. We traverse the E-Graph and compute the max bpx and min wpd for each E-Class, then compute the cost of the current E-Node. If this cost is less than the current min cost of the E-Class, then we update the min cost of the E-Class.
        
        For propagation delays, we want BPD to be high and WPD to be low. While two E-Nodes in the same E-Class can be different, one E-Node will always have the "best" propagation delays. The only case when two nodes will differ is due to temporal vacuity:
            (G[0,10] a) | (G[2,5] a) ==> G[2,5] a
            (F[0,10] a) & (F[2,5] a) ==> F[2,5] a
        where one formula always implies the other in a conjunction/disjunction. The delays of the removed operator are always inclusive of the kept operator (i.e., [2,5] is in [0,10]), so the BPD is higher and WPD is lower for the kept operator. This will always result in lower memory encoding due to the SCQ sizing formula relying on a subtraction of BPD and addition of sibling WPD.

        Consider the following E-Graph (where each E-Class has a single E-Node in it):
 
            op0         op1
            |           |
        ____|______  ___|___
        |         |  |     |
        v         v  v     v
        phi0      phi1     phi2
        (wpd=10)  (wpd=1)  (wpd=5)

        To compute the cost of phi1, we see that phi0 and ph1 are siblings, as are phi1 and phi2, but wouldn't recognize this from traversing op0 and op1 separately. So, we compute each nodes' max sibling WPD as a separate pass.

        """
        reps = {}

        # eclass_id |-> prop. delay
        max_bpd: dict[str, int] = {s:0  for s in self.eclasses.keys()}

        # eclass_id |-> prop. delay
        min_wpd: dict[str, int] = {s:INF  for s in self.eclasses.keys()}
        scq_size: dict[str, int] = {s:0  for s in self.eclasses.keys()}

        # eclass_id |-> min cost
        min_cost: dict[str, Optional[int]] = {s:None  for s in self.eclasses.keys()}

        # Compute max_bpd and min_wpd for each E-Class
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
                interval = enode.get_interval(self.eclasses)

                if not interval:
                    raise ValueError("No 'Interval' for 'Global' operator")

                cur_bpd = min([max_bpd[i] for i in enode.child_eclass_ids]) + interval.lb
                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) == 0:
                    cur_wpd = INF
                else:
                    cur_wpd = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) + interval.ub

                max_bpd[enode.eclass_id] = max(max_bpd[enode.eclass_id], cur_bpd)
                min_wpd[enode.eclass_id] = min(min_wpd[enode.eclass_id], cur_wpd)

        # Compute SCQ size of each E-Class
        for enode in self.traverse():
            if enode.op[0:3] == "Var":
                pass
            elif enode.op[0:3] == "And":
                # need max wpd of all children and second max wpd (for the node with the max wpd)
                cur_max_wpd_1 = max([min_wpd[i] for i in enode.child_eclass_ids])

                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] != cur_max_wpd_1]) == 0:
                    cur_max_wpd_2 = cur_max_wpd_1
                else:
                    cur_max_wpd_2 = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] != cur_max_wpd_1])

                for child_eclass_id in enode.child_eclass_ids:
                    if min_wpd[child_eclass_id] == cur_max_wpd_1:
                        scq_size[child_eclass_id] = max(scq_size[child_eclass_id], max(cur_max_wpd_2 - max_bpd[child_eclass_id], 0) + 1)
                    else:
                        scq_size[child_eclass_id] = max(scq_size[child_eclass_id], max(cur_max_wpd_1 - max_bpd[child_eclass_id], 0) + 1)
            elif enode.op == "Global":
                # Global nodes have no siblings
                for child_eclass_id in enode.child_eclass_ids:
                    scq_size[child_eclass_id] = 1

        # for eclass_id,cost in scq_size.items():
        #     print(f"{self.eclasses[eclass_id]}\n\t= {cost}")

        for enode in self.traverse():
            # The cost of this node is the sum of the costs of its children E-Classes and its own SCQ size
            new_cost = INF
            if enode.op[0:3] == "Var":
                new_cost = scq_size[enode.eclass_id]
            elif enode.op[0:3] == "And":
                new_cost = scq_size[enode.eclass_id] + sum([scq_size[c] for c in enode.child_eclass_ids])
            elif enode.op == "Global":
                new_cost = scq_size[enode.eclass_id] + sum([scq_size[c] for c in enode.child_eclass_ids])

            print(f"{enode.op} : {new_cost}")

            cur_cost = min_cost[enode.eclass_id]

            if not cur_cost or new_cost < cur_cost:
                min_cost[enode.eclass_id] = new_cost
                reps[enode.eclass_id] = enode

        # pprint.pprint(min_cost)

        for eclass_id,cost in [(e,c) for e,c in min_cost.items() if c]:
            print(f"{self.eclasses[eclass_id]}\n\t= {cost}")

        print(f"{self.eclasses[self.root]}  :  {min_cost[self.root]}")

        return reps


def to_egglog(spec: cpt.Formula) -> str:
    """Returns a string that represents `spec` in egglog syntax."""
    egglog = f"(let {spec.symbol[1:]} "

    stack: list["tuple[int, cpt.Expression]"] = []
    stack.append((0, spec.get_expr()))

    while len(stack) > 0:
        (seen, expr) = stack.pop()

        if isinstance(expr, cpt.Bool):
            egglog += expr.symbol
        elif expr.atomic_id > -1:
            egglog += f"(Var \"a{expr.atomic_id}\")"
        elif isinstance(expr, cpt.LogicalNegate):
            if seen == 0:
                egglog += "(Not ("
                stack.append((seen+1, expr))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif isinstance(expr, cpt.Global):
            if seen == 0:
                egglog += f"(Global (Interval {expr.interval.lb} {expr.interval.ub}) "
                stack.append((seen+1, expr))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif isinstance(expr, cpt.Future):
            if seen == 0:
                egglog += f"(Future (Interval {expr.interval.lb} {expr.interval.ub}) "
                stack.append((seen+1, expr))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif isinstance(expr, cpt.Until):
            if seen == 0:
                egglog += f"(Until (Interval {expr.interval.lb} {expr.interval.ub}) "
                stack.append((seen+1, expr))
                stack.append((0, expr.children[1]))
                stack.append((0, expr.children[0]))
            else:
                egglog += ")"
        elif isinstance(expr, cpt.Release):
            log.error("Release not implemented", MODULE_CODE)
        elif isinstance(expr, cpt.LogicalAnd):
            arity = len(expr.children)
            if seen == 0:
                egglog += f"(And{arity} "
                stack.append((seen+1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                egglog += ")"
        elif isinstance(expr, cpt.LogicalOr):
            arity = len(expr.children)
            if seen == 0:
                egglog += f"(Or{arity} "
                stack.append((seen+1, expr))
                [stack.append((0, child)) for child in reversed(expr.children)]
            else:
                egglog += ")"

    return egglog + ")\n"


def run_egglog(spec: cpt.Formula):
    with open(PRELUDE_PATH, "r") as f:
        prelude = f.read()
    
    egglog = prelude + to_egglog(spec) + PRELUDE_END

    with open(TMP_EGG_PATH, "w") as f:
        f.write(egglog)

    command = [str(EGGLOG_PATH), "--to-json", str(TMP_EGG_PATH)]
    subprocess.run(command, capture_output=True)

    with open(EGGLOG_OUTPUT, "r") as f:
        egglog_output = json.load(f)

    egraph = EGraph.from_json(egglog_output)
    egraph.compute_reprs()


