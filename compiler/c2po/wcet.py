from typing import Dict, List, Tuple

from c2po..logger import logger
from c2po.assemble import Operator, FTOperator, PTOperator, BZOperator, Instruction

DEFAULT_CPU_LATENCY_TABLE: Dict[Operator, int] = { op:10 for op in
    [op for op in FTOperator] + [op for op in PTOperator] + [op for op in BZOperator] }

def compute_cpu_wcet(assembly: List[Instruction], latency_table: Dict[str, int], clk: int) -> int:
    """
    Compute and return worst-case execution time in clock cycles for software version R2U2 running on a CPU. Sets this total to the cpu_wcet value of program.

    latency_table is a dictionary that maps the instruction operators to their estimated computation time in CPU clock cycles. For instance, one key-value pair may be (FTOperator.GLOBALLY: 15).
    """
    def compute_cpu_wcet_util(instr: Instruction) -> int:
        nonlocal latency_table
        operator: Optional[Operator] = instr.operator # type: ignore

        if not operator:
            logger.error(f"While computing CPU WCET, found invalid instruction '{instr}'")
            return 0
        elif operator not in latency_table:
            logger.error(f"Operator '{operator.symbol()}' not found in CPU latency table.")
            return 0
        else:
            return int((latency_table[operator] * instr.node.scq_size) / clk)

    return sum([compute_cpu_wcet_util(a) for a in assembly])

DEFAULT_FPGA_LATENCY_TABLE: Dict[Operator, Tuple[float,float]] = { op:(10.0,10.0) for op in
    [op for op in FTOperator] + [op for op in PTOperator] + [op for op in BZOperator] }

def compute_fpga_wcet(assembly: List[Instruction], latency_table: Dict[str, Tuple[float, float]], clk: float) -> float:
    """
    Compute and return worst-case execution time in clock cycles for software version R2U2 running on a CPU. Sets this total to the cpu_wcet value of program.

    latency_table is a dictionary that maps the instruction operators to their estimated computation time in micro seconds. For instance, one key-value pair may be ('FTOperator.GLOBALLY': 15.0).
    """
    wcet: float = 0

    def compute_fpga_wcet_util(instr: Instruction) -> float:
        nonlocal latency_table
        operator: Optional[Operator] = instr.operator # type: ignore

        if not operator:
            logger.error(f"While computing CPU WCET, found invalid instruction '{instr}'")
            return 0
        elif operator not in latency_table:
            logger.error(f"Operator '{operator.symbol()}' not found in CPU latency table.")
            return 0
        else:
            sum_scq_sizeschildren = sum([c.scq_size for c in instr.node.children])
            (init_time, exec_time) = latency_table[operator]
            return init_time + exec_time*sum_scq_sizeschildren

    return sum([compute_fpga_wcet_util(a) for a in assembly])