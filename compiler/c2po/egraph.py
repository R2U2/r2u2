"""
Runs `egglog` (https://github.com/egraphs-good/egglog) to saturate and optimize MLTL memory encoding
"""
from __future__ import annotations
from pathlib import Path
import json
import subprocess

from c2po.ast import *

PRELUDE_EGG_FILE = Path(__file__).parent.parent / "prelude.egg"


def to_egglog(expr: C2POExpression) -> str:
    return ""



def run_egglog(program: C2POProgram):
    command = ["cargo", "run", ]

