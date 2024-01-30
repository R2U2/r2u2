from __future__ import annotations
import subprocess
import pathlib
import os
import dataclasses
import json

from c2po import cpt, log

MODULE_CODE = "EGRF"

FILE_DIR = pathlib.Path(__file__).parent

EGGLOG_PATH = FILE_DIR / "egglog"
PRELUDE_PATH = FILE_DIR / "mltl.egg"

TMP_EGG_PATH = EGGLOG_PATH / "__tmp__.egg"
EGGLOG_OUTPUT = TMP_EGG_PATH.with_suffix(".json")

PRELUDE_END = "(run-schedule (saturate mltl-rewrites))"

@dataclasses.dataclass
class ENode:
    id: str
    op: str
    children: list[int]
    eclass: int

    @staticmethod
    def from_json(id: str, content: dict) -> ENode:
        return ENode(id, content["op"], content["children"], content["eclass"])


class EClass:
    def __init__(self, id: int, nodes: set[ENode]) -> None:
        pass



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


def from_json(content: dict):

    for id,node in content["nodes"].items():
        ENode.from_json(id, node)




def run_egglog(spec: cpt.Formula):
    with open(PRELUDE_PATH, "r") as f:
        prelude = f.read()
    
    os.chdir(EGGLOG_PATH)

    print(pathlib.Path.cwd())

    egglog = prelude + to_egglog(spec) + PRELUDE_END

    with open(TMP_EGG_PATH, "w") as f:
        f.write(egglog)


    command = ["cargo", "run", "--", "--to-json", str(TMP_EGG_PATH)]
    print(command)

    subprocess.run(command)

    with open(EGGLOG_OUTPUT, "r") as f:
        egglog_output = json.load(f)

    from_json(egglog_output)


