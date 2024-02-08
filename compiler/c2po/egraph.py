from __future__ import annotations
import subprocess
import pathlib
import dataclasses
import json
import pprint
from typing import Optional

from c2po import cpt, log, types

MODULE_CODE = "EGRF"

FILE_DIR = pathlib.Path(__file__).parent

EGGLOG_PATH = FILE_DIR / "egglog" / "target" / "debug" / "egglog"
PRELUDE_PATH = FILE_DIR / "mltl.egg"

TMP_EGG_PATH = FILE_DIR / "__tmp__.egg"
EGGLOG_OUTPUT = TMP_EGG_PATH.with_suffix(".json")

PRELUDE_END = "(run-schedule (saturate mltl-rewrites))"

@dataclasses.dataclass
class ENode:
    id: str
    op: str
    children: list[str] # child EClasses
    eclass_id: str

    @staticmethod
    def from_json(id: str, content: dict) -> ENode:
        return ENode(id, content["op"], content["children"], content["eclass"])
    
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, ENode) and self.id ==__value.id
    
    def __hash__(self) -> int:
        return hash(self.id)
    
    def get_interval(self, eclasses: dict[str, set[ENode]]) -> Optional[types.Interval]:
        for child_id in self.children:
            enodes = eclasses[child_id]

            # intervals should only be singletons
            if len(enodes) != 1:
                return None
            
            interval = enodes.pop()
            if interval.op != "Interval":
                return None
            
            # Interval should look like (with lb=4, ub=10):
            # 'interval_id': {ENode(id='...'), op='Interval', children=['lb_id', 'ub_id']}
            # 'lb_id': ENode(id='...', op='4')
            # 'ub_id': ENode(id='...', op='10')
            lb = int(eclasses[interval.children[0]].pop().op)
            ub = int(eclasses[interval.children[1]].pop().op)

            return types.Interval(lb, ub)
        
        # otherwise no children, no interval
        return None


@dataclasses.dataclass
class EGraph:
    root: str
    eclasses: dict[str, set[ENode]]

    @staticmethod
    def from_eclasses(eclasses: dict[str, set[ENode]]) -> EGraph:
        if len(eclasses) < 1:
            log.error("Empty EGraph", MODULE_CODE)
            return EGraph("",{})
        
        parents: dict[str, set[str]] = {i:set() for i in eclasses.keys()}

        for eclass_id,enodes in eclasses.items():
            for enode in enodes:
                for child_eclass_id in enode.children:
                    parents[child_eclass_id].add(eclass_id)

        root_candidates = [id for id,pars in parents.items() if len(pars) == 0]

        if len(root_candidates) == 1:
            return EGraph(root_candidates[0], eclasses)
        elif len(root_candidates) > 1:
            raise ValueError(f"Many root candidates -- possible self-loop back to true root node {root_candidates}")
        else:
            raise ValueError("No root candidates")
        
    @staticmethod
    def from_json(content: dict) -> EGraph:
        enodes: dict[str, ENode] = {}
        eclass_ids: dict[str, str] = {}
        eclasses: dict[str, set[ENode]] = {}

        for enode_id,node in content["nodes"].items():
            eclass_ids[enode_id] = node["eclass"]

        for enode_id,node in content["nodes"].items():
            node["children"] = [eclass_ids[s] for s in node["children"]]
            enode = ENode.from_json(enode_id, node)
            enodes[enode_id] = enode

            if enode.eclass_id not in eclasses:
                eclasses[enode.eclass_id] = {enode}
            else:
                eclasses[enode.eclass_id].add(enode)

        egraph = EGraph.from_eclasses(eclasses)

        pprint.pprint(egraph.eclasses)

        return egraph
    
    def compute_reprs(self) -> dict[str, str]:
        reps = {}

        # eclass_id |--> max best-case prop. delay
        max_bpd: dict[str, int] = {s:0  for s in self.eclasses.keys()}

        # eclass_id |--> min worst-case prop. delay
        min_wpd: dict[str, int] = {s:0  for s in self.eclasses.keys()}

        # eclass_id |--> min cost
        min_cost: dict[str, Optional[int]] = {s:None  for s in self.eclasses.keys()}

        stack: list[ENode] = []
        visited = set()

        [stack.append(enode) for enode in self.eclasses[self.root]]

        while len(stack) > 0:
            cur_enode = stack.pop()

            if cur_enode.op[0:2] == "Var":
                # all e-classes are initialized to 0
                pass
            elif cur_enode.op[0:2] == "And":
                cur_bpd = min([max_bpd[i] for i in cur_enode.children])
                cur_wpd = max([min_wpd[i] for i in cur_enode.children])

                max_bpd[cur_enode.eclass_id] = max(max_bpd[cur_enode.eclass_id], cur_bpd)
                min_wpd[cur_enode.eclass_id] = min(min_wpd[cur_enode.eclass_id], cur_wpd)
            elif cur_enode.op == "Global":
                interval = cur_enode.get_interval(self.eclasses)

                if not interval:
                    raise ValueError("No 'Interval' for 'Global' operator")

                cur_bpd = min([max_bpd[i] for i in cur_enode.children]) + interval.lb
                cur_wpd = max([min_wpd[i] for i in cur_enode.children]) + interval.ub

                max_bpd[cur_enode.eclass_id] = max(max_bpd[cur_enode.eclass_id], cur_bpd)
                min_wpd[cur_enode.eclass_id] = min(min_wpd[cur_enode.eclass_id], cur_wpd)

            cur_cost = 1
            for child in cur_enode.children:
                child_cost = min_cost[child]
                if not child_cost:
                    continue
                cur_cost += child_cost

            cur_min_cost = min_cost[cur_enode.eclass_id]
            if not cur_min_cost or cur_cost < cur_min_cost:
                min_cost[cur_enode.eclass_id] = cur_cost

            if cur_enode.id in visited:
                continue

            stack.append(cur_enode)
            visited.add(cur_enode.id)

            for enode in self.eclasses[cur_enode.eclass_id]:
                for child_eclass_id in [c for c in enode.children if c not in visited]:
                    [stack.append(child) for child in self.eclasses[child_eclass_id]]

        pprint.pprint(min_cost)

        return reps


def to_egglog(spec: cpt.Formula) -> str:
    egglog = f"(let {spec.symbol} "

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

    return egglog + ")"


def run_egglog(spec: cpt.Formula):
    with open(PRELUDE_PATH, "r") as f:
        prelude = f.read()
    
    egglog = prelude + to_egglog(spec) + PRELUDE_END

    with open(TMP_EGG_PATH, "w") as f:
        f.write(egglog)

    command = [str(EGGLOG_PATH), "--to-json", str(TMP_EGG_PATH)]
    subprocess.run(command)

    with open(EGGLOG_OUTPUT, "r") as f:
        egglog_output = json.load(f)

    egraph = EGraph.from_json(egglog_output)
    egraph.compute_reprs()


