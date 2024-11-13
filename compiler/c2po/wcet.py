from __future__ import annotations

from typing import Optional

from c2po import log, assemble

MODULE_CODE = "WCET"


DEFAULT_CPU_LATENCY_TABLE: dict[assemble.Operator, int] = { 
    op:10 
    for op in
    ([op for op in assemble.FTOperator] + 
     [op for op in assemble.PTOperator] + 
     [op for op in assemble.BZOperator])
}


def compute_cpu_wcet(
    assembly: list[assemble.Instruction], 
    latency_table: dict[assemble.Operator, int], 
    clk: int,
) -> int:
    """
    Returns worst-case execution time in clock cycles for formulas running on the software version of R2U2.

    `latency_table` is a dictionary that maps the instruction operators to their estimated computation time in CPU clock cycles. For instance, one key-value pair may be `(FTOperator.GLOBAL: 15)`.
    """
    total_wcet = 0

    for instr in assembly:
        if isinstance(instr, (assemble.ATInstruction, assemble.CGInstruction)):
            continue

        operator: Optional[assemble.Operator] = instr.operator
        if not operator:
            log.error(MODULE_CODE, f"While computing CPU WCET, found invalid instruction '{instr}'")
            return 0
        elif operator not in latency_table:
            log.error(MODULE_CODE, f"Operator '{operator.name}' not found in CPU latency table.")
            return 0
        
        wcet = int((latency_table[operator]) / clk)

        log.debug(MODULE_CODE, 2, f"CPU_WCET({instr}) = {wcet}")

        total_wcet += wcet

    log.stat(MODULE_CODE, f"cpu_wcet={total_wcet}")

    return total_wcet


DEFAULT_FPGA_LATENCY_TABLE: dict[assemble.Operator, tuple[float, float]] = { 
    op:(10.0,10.0) 
    for op in
    ([op for op in assemble.FTOperator] + 
     [op for op in assemble.PTOperator] + 
     [op for op in assemble.BZOperator])
}

def compute_fpga_wcet(assembly: list[assemble.Instruction], latency_table: dict[assemble.Operator, tuple[float, float]], clk: float) -> float:
    """
    Returns worst-case execution time in clock cycles for hardware version R2U2 running on a FPGA.

    `latency_table` is a dictionary that maps the instruction operators to their estimated init/exec times in micro seconds. For instance, one key-value pair may be `('FTOperator.GLOBALLY': (15.0,5.0)).`
    """
    total_wcet = 0

    scq_instrs = [instr for instr in assembly if isinstance(instr, assemble.CGInstruction) and instr.type == assemble.CGType.DUOQ]

    for instr in assembly:
        if isinstance(instr, (assemble.ATInstruction, assemble.CGInstruction)):
            continue

        operator: Optional[assemble.Operator] = instr.operator
        if not operator:
            log.error(MODULE_CODE, f"While computing FPGA WCET, found invalid instruction '{instr}'")
            return 0
        elif operator not in latency_table:
            log.error(MODULE_CODE, f"Operator '{operator.name}' not found in FPGA latency table.")
            return 0
        
        init_time, exec_time = latency_table[operator]
        
        if isinstance(operator, assemble.FTOperator) and isinstance(instr, assemble.TLInstruction):
            sum_children_scq_size = 1

            child_ids = set()
            if instr.operand1_type == assemble.TLOperandType.SUBFORMULA:
                child_ids.add(instr.operand1_value)
            if instr.operand2_type == assemble.TLOperandType.SUBFORMULA:
                child_ids.add(instr.operand2_value)

            for scq_instr in scq_instrs:
                if scq_instr.instruction.operand1_value in child_ids: # type: ignore
                    sum_children_scq_size += scq_instr.instruction.operand2_value
                    break

            wcet = init_time + (exec_time * sum_children_scq_size)
        else:
            wcet = init_time + exec_time

        log.debug(MODULE_CODE, 2, f"FPGA({instr}) = {wcet}")

        total_wcet += wcet

    log.stat(MODULE_CODE, f"fpga_wcet={total_wcet}")

    return total_wcet