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
    has_self_loop: bool = False

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
                    if child_eclass_id == enode.eclass_id:
                        enode.has_self_loop = True
                    parents[child_eclass_id].add(eclass_id)

        root_candidates = [id for id,pars in parents.items() if len(pars) == 0]

        if len(root_candidates) == 1:
            return EGraph(EClassID(root_candidates[0]), eclasses)
        elif len(root_candidates) > 1:
            raise ValueError(f"Many root candidates -- possible self-loop back to true root node {root_candidates}")
        else:
            raise ValueError("No root candidates")
    
    def traverse(self):
        stack: list[tuple[ENode,bool]] = []
        done: set[ENodeID] = set()

        [stack.append((enode, False)) for enode in self.eclasses[self.root]]

        while len(stack) > 0:
            (cur_enode, seen) = stack.pop()

            # print(f"{cur_enode.op} : {seen} : {cur_enode.enode_id in done} : {cur_enode.has_self_loop}\n\t{cur_enode.enode_id}")

            if seen and cur_enode.enode_id not in done:
                done.add(cur_enode.enode_id)
                yield cur_enode
                continue
            elif cur_enode.enode_id in done:
                continue

            stack.append((cur_enode, True))
            # print(f"1: {cur_enode.op} ({cur_enode.enode_id})")

            for enode in [e for e in self.eclasses[cur_enode.eclass_id] if not e.has_self_loop]:
                for child_eclass_id in enode.child_eclass_ids:
                    # for child in self.eclasses[child_eclass_id]:
                    #     if not child.has_self_loop:
                    #         print(f"2: {child.op} ({child.enode_id})")
                    [stack.append((child, False)) for child in self.eclasses[child_eclass_id] if not child.has_self_loop]

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
            if enode.op in {"Bool", "true", "false", "Var"}:
                max_bpd[enode.eclass_id] = 0
                min_wpd[enode.eclass_id] = 0
            elif enode.op == "Not":
                operand_eclass_id = enode.child_eclass_ids[0]
                max_bpd[enode.eclass_id] = max_bpd[operand_eclass_id]
                min_wpd[enode.eclass_id] = min_wpd[operand_eclass_id]
            elif enode.op[0:3] == "And" or enode.op[0:2] == "Or" or enode.op == "Equiv" or enode.op == "Implies":
                cur_bpd = min([max_bpd[i] for i in enode.child_eclass_ids])

                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) == 0:
                    cur_wpd = INF
                else:
                    cur_wpd = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF])

                max_bpd[enode.eclass_id] = max(max_bpd[enode.eclass_id], cur_bpd)
                min_wpd[enode.eclass_id] = min(min_wpd[enode.eclass_id], cur_wpd)
            elif enode.op == "Global" or enode.op == "Future":
                interval = enode.interval
                if not interval:
                    raise ValueError(f"No 'Interval' for operator {enode.op}")

                cur_bpd = min([max_bpd[i] for i in enode.child_eclass_ids]) + interval.lb
                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) == 0:
                    cur_wpd = INF
                else:
                    cur_wpd = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) + interval.ub

                max_bpd[enode.eclass_id] = max(max_bpd[enode.eclass_id], cur_bpd)
                min_wpd[enode.eclass_id] = min(min_wpd[enode.eclass_id], cur_wpd)
            elif enode.op == "Until":
                interval = enode.interval
                if not interval:
                    raise ValueError(f"No 'Interval' for operator {enode.op}")

                cur_bpd = min([max_bpd[i] for i in enode.child_eclass_ids]) + interval.lb
                if len([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) == 0:
                    cur_wpd = INF
                else:
                    cur_wpd = max([min_wpd[i] for i in enode.child_eclass_ids if min_wpd[i] < INF]) + interval.ub

                max_bpd[enode.eclass_id] = max(max_bpd[enode.eclass_id], cur_bpd)
                min_wpd[enode.eclass_id] = min(min_wpd[enode.eclass_id], cur_wpd)
            else:
                raise ValueError(f"Invalid node type for PD computation {enode.op}")

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
            if enode.op in {"Bool", "true", "false", "Var"}:
                # no children, so 0
                cost[enode.enode_id] = 1
            elif enode.op[0:3] == "And" or enode.op[0:2] == "Or" or enode.op == "Equiv" or enode.op == "Implies" or enode.op == "Until":
                total_cost = 1

                # need max wpd of all children and second max wpd (for the node with the max wpd)
                min_wpds = [min_wpd[i] for i in enode.child_eclass_ids]
                cur_max_wpd_1 = max(min_wpds)
                min_wpds.remove(cur_max_wpd_1)
                cur_max_wpd_2 = max(min_wpds)

                for child_eclass_id in enode.child_eclass_ids:
                    if min_wpd[child_eclass_id] == cur_max_wpd_1:
                        total_cost += max(cur_max_wpd_2 - max_bpd[child_eclass_id], 0) 
                    else:
                        total_cost += max(cur_max_wpd_1 - max_bpd[child_eclass_id], 0) 

                cost[enode.enode_id] = total_cost
            elif enode.op in {"Global", "Future", "Not"}:
                # Global nodes have *lonely* single children (no siblings)
                cost[enode.enode_id] = 1
            else:
                raise ValueError(f"Invalid node type for cost computation {enode.op}")

        return cost
    
    def build_expr_tree(
            self, 
            rep: dict[EClassID, tuple[ENode, int]], 
            eclass: EClassID, 
            atomics: dict[cpt.Expression, int]
    ) -> cpt.Expression:
        enode,_ = rep[eclass]

        if enode.op == "Bool":
            return cpt.Constant(log.EMPTY_FILE_LOC, True)
        elif enode.op[0:3] == "Var":
            if not enode.string:
                raise ValueError("No string for Var")
            
            # map back to the expression this atomic points to
            atomic_id = int(enode.string.replace('"','')[1:])

            try:
                expr = next(e for e,i in atomics.items() if i == atomic_id)
                return expr
            except StopIteration:
                log.internal(f"No atomic found with id {atomic_id}", MODULE_CODE)
                return cpt.Constant(log.EMPTY_FILE_LOC, False)
        elif enode.op == "Not":
            operand = self.build_expr_tree(rep, enode.child_eclass_ids[0], atomics)
            return cpt.Operator.LogicalNegate(log.EMPTY_FILE_LOC, operand)
        elif enode.op[0:3] == "And":
            ch = [self.build_expr_tree(rep, c, atomics) for c in enode.child_eclass_ids]
            return cpt.Operator.LogicalAnd(log.EMPTY_FILE_LOC, ch)
        elif enode.op[0:2] == "Or":
            ch = [self.build_expr_tree(rep, c, atomics) for c in enode.child_eclass_ids]
            return cpt.Operator.LogicalOr(log.EMPTY_FILE_LOC, ch)
        elif enode.op == "Equiv":
            lhs = self.build_expr_tree(rep, enode.child_eclass_ids[0], atomics)
            rhs = self.build_expr_tree(rep, enode.child_eclass_ids[1], atomics)
            return cpt.Operator.LogicalIff(log.EMPTY_FILE_LOC, lhs, rhs)
        elif enode.op == "Implies":
            lhs = self.build_expr_tree(rep, enode.child_eclass_ids[0], atomics)
            rhs = self.build_expr_tree(rep, enode.child_eclass_ids[1], atomics)
            return cpt.Operator.LogicalImplies(log.EMPTY_FILE_LOC, lhs, rhs)
        elif enode.op == "Global":
            ch = [self.build_expr_tree(rep, c, atomics) for c in enode.child_eclass_ids]
            ch = ch[0]
            if not enode.interval:
                raise ValueError("No Interval for Global")
            return cpt.TemporalOperator.Global(log.EMPTY_FILE_LOC, enode.interval.lb, enode.interval.ub, ch)
        elif enode.op == "Future":
            ch = [self.build_expr_tree(rep, c, atomics) for c in enode.child_eclass_ids]
            ch = ch[0]
            if not enode.interval:
                raise ValueError("No Interval for Future")
            return cpt.TemporalOperator.Future(log.EMPTY_FILE_LOC, enode.interval.lb, enode.interval.ub, ch)
        elif enode.op == "Until":
            ch = [self.build_expr_tree(rep, c, atomics) for c in enode.child_eclass_ids]
            ch0 = ch[0]
            ch1 = ch[1]
            if not enode.interval:
                raise ValueError("No Interval for Until")
            return cpt.TemporalOperator.Until(log.EMPTY_FILE_LOC, enode.interval.lb, enode.interval.ub, ch0 ,ch1)
        elif enode.op == "Release":
            ch = [self.build_expr_tree(rep, c, atomics) for c in enode.child_eclass_ids]
            ch0 = ch[0]
            ch1 = ch[1]
            if not enode.interval:
                raise ValueError("No Interval for Release")
            return cpt.TemporalOperator.Release(log.EMPTY_FILE_LOC, enode.interval.lb, enode.interval.ub, ch0 ,ch1)
        else:
            raise ValueError(f"Invalid node type {enode.op}")

    def extract(self, context: cpt.Context) -> cpt.Expression:
        rep: dict[EClassID, tuple[ENode, int]] = {}

        cost: dict[ENodeID, int] = self.compute_cost()
        total_cost: dict[ENodeID, int] = {}

        # TODO: can the rep for an EClass change after one of its parents' rep has been computed?
        for enode in self.traverse():
            child_costs = sum([total_cost[rep[c][0].enode_id] for c in enode.child_eclass_ids]) 
            total_cost[enode.enode_id] = cost[enode.enode_id] + child_costs

            if enode.eclass_id not in rep or total_cost[enode.enode_id] < rep[enode.eclass_id][1]:
                rep[enode.eclass_id] = (enode, total_cost[enode.enode_id])

        expr_tree = self.build_expr_tree(rep, self.root, context.atomic_id)

        log.debug(f"Optimal expression: {repr(expr_tree)}", MODULE_CODE)
        log.debug(f"Cost: {rep[self.root][1]+1}", MODULE_CODE)

        return expr_tree


def to_egglog(spec: cpt.Formula, context: cpt.Context) -> str:
    """Returns a string that represents `spec` in egglog syntax."""
    # egglog = f"(let {spec.symbol[1:] if spec.symbol[0] == '#' else spec.symbol} "
    egglog = ""
    
    expr_cnt = 0
    expr_map = {}

    stack: list["tuple[int, cpt.Expression]"] = []
    stack.append((0, spec.get_expr()))

    for expr in cpt.postorder(spec, context):
        expr_map[expr] = expr_cnt
        expr_cnt += 1

        if isinstance(expr, cpt.Constant):
            egglog += f"(let e{expr_map[expr]} (Bool {expr.symbol.lower()}))\n"
        elif expr in context.atomic_id:
            egglog += f"(let e{expr_map[expr]} (Var \"a{context.atomic_id[expr]}\"))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            egglog += f"(let e{expr_map[expr]} (Not e{expr_map[expr.children[0]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            egglog += f"(let e{expr_map[expr]} (Implies e{expr_map[expr.children[0]]} e{expr_map[expr.children[1]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            egglog += f"(let e{expr_map[expr]} (Equiv e{expr_map[expr.children[0]]} e{expr_map[expr.children[1]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            egglog += f"(let e{expr_map[expr]} (Global (Interval {expr.interval.lb} {expr.interval.ub}) e{expr_map[expr.children[0]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            egglog += f"(let e{expr_map[expr]} (Future (Interval {expr.interval.lb} {expr.interval.ub}) e{expr_map[expr.children[0]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            egglog += f"(let e{expr_map[expr]} (Until (Interval {expr.interval.lb} {expr.interval.ub}) e{expr_map[expr.children[0]]} e{expr_map[expr.children[1]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error("Release not implemented", MODULE_CODE)
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            arity = len(expr.children)
            egglog += f"(let e{expr_map[expr]} (And{arity} {' '.join([f'e{expr_map[c]}' for c in expr.children])}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            arity = len(expr.children)
            egglog += f"(let e{expr_map[expr]} (Or{arity} {' '.join([f'e{expr_map[c]}' for c in expr.children])}))\n"

    return egglog + "\n"


def run_egglog(spec: cpt.Formula, context: cpt.Context) -> Optional[EGraph]:
    with open(PRELUDE_PATH, "r") as f:
        prelude = f.read()
    
    egglog = prelude + to_egglog(spec, context) + PRELUDE_END

    with open(TMP_EGG_PATH, "w") as f:
        f.write(egglog)

    command = [str(EGGLOG_PATH), "--to-json", str(TMP_EGG_PATH)]
    log.debug(f"Running command '{' '.join(command)}'", MODULE_CODE)
    proc = subprocess.run(command, capture_output=True)

    if proc.returncode:
        log.error(f"Error running egglog\n{proc.stderr.decode()}", MODULE_CODE)
        return None

    with open(EGGLOG_OUTPUT, "r") as f:
        egglog_output = json.load(f)

    egraph = EGraph.from_json(egglog_output)

    return egraph