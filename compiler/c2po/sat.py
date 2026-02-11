import subprocess
import enum
import sys
import math
import pathlib
import shutil
import tempfile
from typing import cast, Any, Optional
from c2po import cpt, log, util, types, stats, command

PREAMBLE = f"""(set-info :source |SMT encoding for satisfiability checking of Mission-time Linear Temporal Logic (MLTL) formulas.
Encoded by C2PO v{log.VERSION}, see https://github.com/R2U2/r2u2/tree/develop/compiler.|)"""

class SatResult(enum.Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"
    TIMEOUT = "timeout"
    MEMOUT = "memout"
    FAILURE = "fail"

def check_sat_result(result: SatResult) -> bool:
    """Checks the result of a SMT solver and returns True if the result is SAT, UNSAT, or UNKNOWN, False otherwise."""
    return result in [SatResult.SAT, SatResult.UNSAT, SatResult.UNKNOWN]

class SMTTheory(enum.Enum):
    UFLIA = "uflia"
    QF_UFLIA = "qf_uflia"
    QF_BV = "qf_bv"

def find_smt_solver() -> Optional[str]:
    """Finds the SMT solver in the PATH. Returns the path to the SMT solver if found, otherwise returns None."""
    for solver in ["z3", "cvc5", "yices-smt2", "mathsat", "bitwuzla"]:
        smt_solver_path = shutil.which(solver)
        if smt_solver_path is not None:
            return smt_solver_path if util.check_executable(smt_solver_path) else None
    return None

def run_smt_solver(
    smt_encoding: str,
    theory: SMTTheory,
    max_time: int,
    max_memory: int,
    stats: stats.Stats,
) -> SatResult:
    """Runs the SMT solver on the given SMT-LIB2 encoding string and returns the result."""
    log.debug(2, "running SMT solver.")

    smt_solver_path = find_smt_solver()
    if smt_solver_path is None:
        log.error("could not find SMT solver")
        return SatResult.FAILURE

    # TODO: Add options to the command, will have to address list[str] type for command parser
    # command = [smt_solver_path] + [opt.replace('"', '') for opt in smt_options]
    command = [smt_solver_path]
    
    if (
        theory == SMTTheory.UFLIA
        or theory == SMTTheory.QF_UFLIA
    ) and "cvc5" in smt_solver_path:
        # cvc5 requires the --finite-model-find option for UFLIA encoding
        command += ["--finite-model-find", "--fmf-bound"]
    
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_file = f"{temp_dir}/tmp.smt2"
        with open(temp_file, "w") as f:
            f.write(smt_encoding)
        command += [temp_file]

        log.debug(2, f"running '{' '.join(command)}'")

        start_time = util.get_children_rusage_time()
        try:
            proc = subprocess.Popen(
                command,
                preexec_fn=util.set_max_memory_offset(max_memory),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
        except OSError as e:
            log.internal(f"error running command '{' '.join(command)}': {e}")
            return SatResult.FAILURE

        try:
            (stdout, stderr) = proc.communicate(timeout=max_time)
        except subprocess.TimeoutExpired:
            proc.kill()
            log.warning(f"{smt_solver_path} timed out")
            return SatResult.TIMEOUT
    
    end_time = util.get_children_rusage_time()
    stdout = stdout.decode() if stdout else ""
    stderr = stderr.decode() if stderr else ""

    if proc.returncode != 0:
        # z3 memout: 
        #   stdout=
        #   stderr=(error "out of memory")
        #   returncode=101
        if "z3" in smt_solver_path and "(error \"out of memory\")" in stderr:
            log.warning(f"{smt_solver_path} ran out of memory")
            return SatResult.MEMOUT

        # cvc5 memout: 
        #   stdout(error "std::bad_alloc")
        #   stderr=
        #   returncode=1
        if "cvc5" in smt_solver_path and "std::bad_alloc" in stdout or "std::bad_alloc" in stderr:
            log.warning(f"{smt_solver_path} ran out of memory")
            return SatResult.MEMOUT

        # yices memout:
        #   stdout=
        #   stderr=out of memory
        #   returncode=16
        if "yices" in smt_solver_path and "Out of memory" in stderr:
            log.warning(f"{smt_solver_path} ran out of memory")
            return SatResult.MEMOUT

        # mathsat memout
        #   stdout=
        #   stderr=
        #   returncode=6
        if "mathsat" in smt_solver_path and proc.returncode == -6:
            log.warning(f"{smt_solver_path} ran out of memory")
            return SatResult.MEMOUT

        # bitwuzla memout
        #   stdout=
        #   stderr=terminate called after throwing an instance of 'std::bad_alloc'
        #            what():  std::bad_alloc
        #   returncode=-6
        if "bitwuzla" in smt_solver_path and "std::bad_alloc" in stderr:
            log.warning(f"{smt_solver_path} ran out of memory")
            return SatResult.MEMOUT
        
        log.error(
            f"{smt_solver_path} failed with return code {proc.returncode}",
        )
        log.debug(2, "stdout:" + stdout[:-1])
        log.debug(2, "stderr:" + stderr[:-1])
        return SatResult.FAILURE

    if stdout.find("unsat") > -1:
        log.debug(2, "unsat")
        result = SatResult.UNSAT
    elif stdout.find("sat") > -1:
        log.debug(2, "sat")
        result = SatResult.SAT
    else:
        log.debug(2, "unknown")
        result = SatResult.UNKNOWN

    stats.smt_solver_time += end_time - start_time
    stats.smt_num_calls += 1
    stats.smt_solver_result = result.value

    return result

def to_smt_type(t: types.Type) -> str:
    """Convert a C2PO type to an SMT type."""
    if isinstance(t, types.BoolType):
        return "Bool"
    if isinstance(t, types.IntType):
        return "Int"
    if isinstance(t, types.FloatType):
        return "Real"
    return "NoType"

def to_qf_bv_smtlib2(start: cpt.Expression, context: cpt.Context, strict: bool) -> Optional[str]:
    """Encodes the given expression into an SMT encoding using the QF_BV theory and returns it. Returns None if the encoding fails."""
    log.debug(
        1, f"encoding MLTL formula in QF_BV logic (strict: {strict}):\n\t{repr(start)}",
    )

    if len(context.bounds) > 0 or len(context.constraints) > 0:
        log.error("symbolic bounds and constraints are not supported for QF_BV encoding")
        return None

    bv_width = start.wpd + 1 # proxy for cplen
    bv_sort = f"(_ BitVec {bv_width})"

    # Need to set this in case bv literals have more than 4300 digits (in decimal) for to_bv
    # 0 means no limit
    sys.set_int_max_str_digits(0) 

    def to_bv(value: int):
        nonlocal bv_width
        return f"(_ bv{min(value, (2**bv_width) - 1)} {bv_width})"

    def ones():
        nonlocal bv_width
        return f"(_ bv{2**bv_width - 1} {bv_width})"

    def zeros():
        nonlocal bv_width
        return f"(_ bv0 {bv_width})"

    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic QF_BV)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal in context.signals.keys():
        atomic_map[signal] = f"f_{signal}"
        smt_commands.append(f"(declare-fun f_{signal} () {bv_sort})")

    for variable in context.variables.keys():
        atomic_map[variable] = f"f_{variable}"
        smt_commands.append(f"(declare-fun f_{variable} () {bv_sort})")

    # TODO: Remove since we do not need to decompose intervals for QF_BV encoding
    decomposed_expr = cpt.decompose_intervals(start, context)

    status = True
    for expr in cpt.postorder(decomposed_expr, context):
        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        if expr.type != types.BoolType():
            log.error(f"unsupported type '{expr.type}' for expression {expr}")
            status = False
            continue

        fun_signature = "define-fun {0} () " + bv_sort

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature.format(expr_id)} {ones()})")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature.format(expr_id)} {zeros()})")
        elif isinstance(expr, (cpt.Signal, cpt.Variable)):
            smt_commands.append(f"({fun_signature.format(expr_id)} {atomic_map[expr.symbol]})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature.format(expr_id)} (bvnot {expr_map[expr.children[0]]}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            op = f"(bvand {expr_map[expr.children[0]]} {expr_map[expr.children[1]]})"
            for child in expr.children[2:]:
                op = f"(bvand {op} {expr_map[child]})"
            smt_commands.append(f"({fun_signature.format(expr_id)} {op})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            op = f"(bvor {expr_map[expr.children[0]]} {expr_map[expr.children[1]]})"
            for child in expr.children[2:]:
                op = f"(bvor {op} {expr_map[child]})"
            smt_commands.append(f"({fun_signature.format(expr_id)} {op})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature.format(expr_id)} (bvxnor {expr_map[expr.children[0]]} {expr_map[expr.children[1]]}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            child = expr.children[0]
            lb = expr.interval.lb
            ub = expr.interval.ub
            i = 0

            if ub == 0:
                # then expr is G[0,0] phi
                smt_commands.append(
                    f"({fun_signature.format(expr_id)} {expr_map[child]})"
                )
                continue
            elif lb > 0:
                # then expr is G[a,a+2^k-1] phi
                shift_amt = lb
                shift_ones_bitmask = to_bv(2**shift_amt - 1)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvor (bvshl {expr_map[expr.children[0]]} {to_bv(shift_amt)}) {shift_ones_bitmask}))"
                )
                i += 1
                ub -= lb

            for j in range(0, int(math.log2(ub+1))):
                shift_amt = 2**j
                shift_ones_bitmask = to_bv(2**shift_amt - 1)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvor (bvshl {f'{expr_id}_{i-1}' if i > 0 else expr_map[expr.children[0]]} {to_bv(shift_amt)}) {shift_ones_bitmask}))"
                )
                i += 1
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvand {f'{expr_id}_{i-1}'} {f'{expr_id}_{i-2}' if i > 1 else expr_map[expr.children[0]]}))"
                )
                i += 1

            smt_commands.append(
                f"({fun_signature.format(expr_id)} {f'{expr_id}_{i-1}'})"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            child = expr.children[0]
            lb = expr.interval.lb
            ub = expr.interval.ub
            i = 0

            if ub == 0:
                smt_commands.append(
                    f"({fun_signature.format(expr_id)} {expr_map[child]})"
                )
                continue
            elif lb > 0:
                shift_amt = lb
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvshl {expr_map[expr.children[0]]} {to_bv(shift_amt)}))"
                )
                i += 1
                ub -= lb

            for j in range(0, int(math.log2(ub+1))):
                shift_amt = 2**j
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvshl {f'{expr_id}_{i-1}' if i > 0 else expr_map[expr.children[0]]} {to_bv(shift_amt)}))"
                )
                i += 1
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvor {f'{expr_id}_{i-1}'} {f'{expr_id}_{i-2}' if i > 1 else expr_map[expr.children[0]]}))"
                )
                i += 1

            smt_commands.append(
                f"({fun_signature.format(expr_id)} {f'{expr_id}_{i-1}'})"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lhs = expr.children[0]
            rhs = expr.children[1]
            lb = expr.interval.lb
            ub = expr.interval.ub
            i = 0
            j = 0

            if ub == 0:
                smt_commands.append(
                    f"({fun_signature.format(expr_id)} {expr_map[rhs]})"
                )
                continue
            elif lb > 0:
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_L_{j}')} (bvshl {expr_map[lhs]} {to_bv(lb)}))"
                )
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i}')} (bvshl {expr_map[rhs]} {to_bv(lb)}))"
                )
                i += 1
                j += 1
                ub -= lb
             
            for k in range(0, int(math.log2(ub+1))):
                # expr_R = expr_R_{j} | (expr_L_{i-1} & (expr_R_{j} << 2^k))
                # (expr_R_{i} << 1)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i}')} (bvshl {f'{expr_id}_R_{i-1}' if i > 0 else expr_map[rhs]} {to_bv(2**k)}))"
                )
                # (expr_L_{j-1} & (expr_R_{i} << 2^k))
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i+1}')} (bvand {f'{expr_id}_R_{i}'} {f'{expr_id}_L_{j-1}' if j > 0 else expr_map[lhs]}))"
                )
                # expr_R_{i} | (expr_L_{j-1} & (expr_R_{i} << 2^k))
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i+2}')} (bvor {f'{expr_id}_R_{i+1}'} {f'{expr_id}_R_{i-1}' if i > 0 else expr_map[rhs]}))"
                )
                i += 3

                # expr_L = expr_L_{j-1} & (expr_L_{j-1} << 2^k)
                # expr_L_{j-1} << 2^k
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_L_{j}')} (bvshl {f'{expr_id}_L_{j-1}' if j > 0 else expr_map[lhs]} {to_bv(2**k)}))"
                )
                # expr_R_{j-1} & (expr_R_{j-1} << 2^k)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_L_{j+1}')} (bvand {f'{expr_id}_L_{j}'} {f'{expr_id}_L_{j-1}' if j > 0 else expr_map[lhs]}))"
                )
                j += 2

            smt_commands.append(
                f"({fun_signature.format(expr_id)} {f'{expr_id}_R_{i-1}'})"
            )
        else:
            log.error(f"unsupported expression {expr}")
            status = False
            continue

    if not status:
        return None

    if strict:
        smt_commands.append(f"(assert (bvugt {expr_map[decomposed_expr]} {zeros()}))")
    else:
        smt_commands.append(f"(assert (= ((_ extract {start.wpd} {start.wpd}) {expr_map[decomposed_expr]}) (_ bv1 1)))")

    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt

def to_qf_uflia_smtlib2(start: cpt.Expression, context: cpt.Context, strict: bool) -> Optional[str]:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the QF_UFLIA logic."""
    log.debug(
        1, f"encoding MLTL formula in QF_UFLIA logic (strict: {strict}):\n\t{repr(start)}"
    )

    if len(context.bounds) > 0 or len(context.constraints) > 0:
        log.error("symbolic bounds and constraints are not supported for QF_UFLIA encoding")
        return None

    is_nonlinear: bool = False
    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic QF_UFLIA)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        smt_commands.append(f"(declare-fun f_{signal} (Int) {to_smt_type(typ)})")

    for variable in context.variables.keys():
        atomic_map[variable] = f"p_{variable}"
        smt_commands.append(f"(declare-fun p_{variable} (Int) {to_smt_type(context.variables[variable])})")

    status = True
    for expr in cpt.postorder(start, context):
        if expr.type != types.BoolType() and expr.type != types.IntType():
            log.error(f"unsupported type '{expr.type}' for expression {expr}")
            status = False
            continue
        
        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        fun_signature = (
            f"define-fun {expr_id} ((k Int) (len Int)) {to_smt_type(expr.type)}"
        )

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and expr.value:
            smt_commands.append(f"({fun_signature} true)")
        elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and not expr.value:
            smt_commands.append(f"({fun_signature} false)")
        elif isinstance(expr, cpt.Constant):
            smt_commands.append(f"({fun_signature} {expr.value})")
        elif isinstance(expr, cpt.Signal) and types.is_bool_type(expr.type):
            smt_commands.append(
                f"({fun_signature} (and (> len k) ({atomic_map[expr.symbol]} k)))"
            )
        elif isinstance(expr, (cpt.Signal, cpt.Variable)):
            smt_commands.append(f"({fun_signature} ({atomic_map[expr.symbol]} k))")
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
            smt_commands.append(
                f"({fun_signature} (+ ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (* ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (div ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (mod ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (>= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (< ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (<= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not ({expr_map[expr.children[0]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and (> len k) {operands}))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (and (> len k) (or {operands})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            conds = [
                f"(=> (> len (+ k {i})) ({expr_map[expr.children[0]]} (+ k {i}) len))"
                for i in range(lb, ub + 1)
            ]
            smt_commands.append(
                f"({fun_signature} "
                f"(and (> len k) (or (<= len (+ {lb} k)) "
                f"(and {' '.join(conds)}))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            conds = [
                f"({expr_map[expr.children[0]]} (+ k {i}) len)"
                for i in range(lb, ub + 1)
            ]
            smt_commands.append(
                f"({fun_signature} "
                f"(and (> len (+ {lb} k)) "
                f"(or {' '.join(conds)})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub

            unroll = f"({expr_map[expr.children[1]]} (+ {ub} k) len)"
            for i in reversed(range(lb, ub)):
                unroll = f"(or ({expr_map[expr.children[1]]} (+ {i} k) len) (and ({expr_map[expr.children[0]]} (+ {i} k) len) {unroll}))"

            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) {unroll}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(
                f"release not implemented for MLTL-SAT via QF_UFLIA\n\t{expr}"
            )
            status = False
            continue
        else:
            log.error(f"unsupported expression {expr}")
            status = False
            continue

    if not status:
        return None

    if strict:
        smt_commands.append("(declare-fun len () Int)")
        smt_commands.append(f"(assert ({expr_map[start]} 0 len))")
    else:
        # wpd proxy for cplen (okay since wpd >= cplen)
        smt_commands.append(f"(assert ({expr_map[start]} 0 {start.wpd}))")

    smt_commands.append("(check-sat)")

    if is_nonlinear:
        log.warning("nonlinear arithmetic detected, setting logic to QF_UFNIA")
        smt_commands[1] = "(set-logic QF_UFNIA)"

    smt = "\n".join(smt_commands)

    return smt

def to_uflia_smtlib2(
    start: cpt.Expression,
    context: cpt.Context,
    strict: bool,
) -> Optional[str]:
    """Encodes the given expression into an SMT encoding using the UFLIA theory and returns it. Returns None if the encoding fails."""
    log.debug(2, f"bounds: {context.bounds}")
    log.debug(2, f"constraints: {context.constraints}")
    is_nonlinear: bool = False
    has_mission_time: bool = False
    status: bool = True

    def smt_min_expr(expr1: str, expr2: str) -> str:
        return f"(ite (<= {expr1} {expr2}) {expr1} {expr2})"

    def smt_max_expr(expr1: str, expr2: str) -> str:
        return f"(ite (>= {expr1} {expr2}) {expr1} {expr2})"

    def interval_constraint_to_smt(constraint: cpt.Expression, cache: dict[cpt.Expression, str]) -> str:
        nonlocal is_nonlinear
        nonlocal has_mission_time
        nonlocal status

        for expr in cpt.postorder(constraint, context):
            if expr in cache:
                continue
            if isinstance(expr, cpt.SymbolicIntervalVariable):
                cache[expr] = expr.symbol
            elif isinstance(expr, cpt.MissionTime):
                cache[expr] = "M"
                has_mission_time = True
            elif isinstance(expr, cpt.Constant):
                cache[expr] = str(expr.value)
            elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
                cache[expr] = f"(= {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
                cache[expr] = f"(not (= {cache[expr.children[0]]} {cache[expr.children[1]]}))"
            elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
                cache[expr] = f"(> {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
                cache[expr] = f"(>= {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
                cache[expr] = f"(< {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
                cache[expr] = f"(<= {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
                cache[expr] = f"(+ {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
                cache[expr] = f"(- {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
                is_nonlinear = True
                cache[expr] = f"(* {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
                is_nonlinear = True
                cache[expr] = f"(/ {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
                is_nonlinear = True
                cache[expr] = f"(mod {cache[expr.children[0]]} {cache[expr.children[1]]})"
            elif cpt.is_operator(expr, cpt.OperatorKind.MIN):
                cache[expr] = smt_min_expr(cache[expr.children[0]], cache[expr.children[1]])
            elif cpt.is_operator(expr, cpt.OperatorKind.MAX):
                cache[expr] = smt_max_expr(cache[expr.children[0]], cache[expr.children[1]])
            else:
                log.error(f"unsupported constraint expression {expr} {type(expr)}")
                status = False
                return ""

        return cache[constraint]

    def expr_to_smt(
        expr: cpt.Expression,
        cnt: int,
        expr_map: dict[cpt.Expression, str],
        expr_cache: dict[str, cpt.Expression],
        constr_cache: dict[cpt.Expression, str],
    ) -> str:
        """Converts an expression to an SMT-LIB2 encoding using the given expression map, expression cache, and constraint cache."""
        nonlocal is_nonlinear
        nonlocal has_mission_time
        nonlocal status

        if expr.type != types.BoolType() and expr.type != types.IntType():
            log.error(f"unsupported type '{expr.type}' ({expr})")
            status = False
            return ""

        if str(expr) in expr_cache:
            expr_map[expr] = expr_map[expr_cache[str(expr)]]
            return ""

        expr_id = f"f_e{cnt}"
        expr_map[expr] = expr_id
        expr_cache[str(expr)] = expr

        fun_signature = (
            f"define-fun {expr_id} ((k Int) (len Int)) {to_smt_type(expr.type)}"
        )

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and expr.value:
            return f"({fun_signature} true)"
        elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and not expr.value:
            return f"({fun_signature} false)"
        elif isinstance(expr, cpt.Constant):
            return f"({fun_signature} {expr.value})"
        elif isinstance(expr, (cpt.Signal, cpt.Variable)) and types.is_bool_type(expr.type):
            return f"({fun_signature} (and (> len k) ({atomic_map[expr.symbol]} k)))"
        elif isinstance(expr, (cpt.Signal, cpt.Variable)):
            return f"({fun_signature} ({atomic_map[expr.symbol]} k))"
        elif isinstance(expr, cpt.Atomic):
            return f"({fun_signature} (and (> len k) ({expr_map[expr.children[0]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
            return f"({fun_signature} (+ ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT) and len(expr.children) == 2:
            return f"({fun_signature} (- ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT) and len(expr.children) == 1:
            # FIXME: Somewhere arithmetic negation is being encoded as arithmetic subtract with one operand
            return f"({fun_signature} (- ({expr_map[expr.children[0]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
            is_nonlinear = True
            return f"({fun_signature} (* ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            is_nonlinear = True
            return f"({fun_signature} (div ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
            is_nonlinear = True
            return f"({fun_signature} (mod ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
            return f"({fun_signature} (- ({expr_map[expr.children[0]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            return f"({fun_signature} (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
            return f"({fun_signature} (not (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
            return f"({fun_signature} (> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
            return f"({fun_signature} (>= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            return f"({fun_signature} (< ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            return f"({fun_signature} (<= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return f"({fun_signature} (not ({expr_map[expr.children[0]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join([f"({expr_map[child]} k len)" for child in expr.children])
            return f"({fun_signature} (and {operands}))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join([f"({expr_map[child]} k len)" for child in expr.children])
            return f"({fun_signature} (or {operands}))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            return f"({fun_signature} (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            return f"({fun_signature} (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            # pi,k |= G[lb,ub] p iff for all i such that lb+k <= i <= ub+k it holds that pi,i |= p
            result = ""
            if isinstance(expr, cpt.SymbolicTemporalOperator):
                # If symbolic constraints are used we need to assert that the lower bound is less than or equal to the upper bound
                expr = cast(cpt.SymbolicTemporalOperator, expr)
                lb = interval_constraint_to_smt(expr.interval.lb, constr_cache)
                ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)

                # Special case for G[0,0] phi and G[1,1] phi -- no need for quantifier
                # This is necessary for performance reasons, many FRET formulas timeout without this optimization
                if lb == "0" and ub == "0":
                    return f"({fun_signature} (or (<= len k) ({expr_map[expr.children[0]]} k len)))"
                elif lb == "1" and ub == "1":
                    return f"({fun_signature} (or (<= len (+ 1 k)) ({expr_map[expr.children[0]]} (+ 1 k) len)))"

                result = f"(assert (<= {lb} {ub}))\n"
            else: 
                expr = cast(cpt.TemporalOperator, expr)
                lb = expr.interval.lb
                ub = expr.interval.ub

                if lb == 0 and ub == 0:
                    return f"({fun_signature} (or (<= len k) ({expr_map[expr.children[0]]} k len)))"
                elif lb == 1 and ub == 1:
                    return f"({fun_signature} (or (<= len (+ 1 k)) ({expr_map[expr.children[0]]} (+ 1 k) len)))"

            return result + f"({fun_signature} (or (<= len (+ {lb} k)) (forall ((i Int)) (=> (and (<= (+ {lb} k) i) (<= i (+ {ub} k))) ({expr_map[expr.children[0]]} i len)))))"
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            # pi,k |= F[lb,ub] p iff there exists i such that lb+k <= i <= ub+k and pi,i |= p
            result = ""
            if isinstance(expr, cpt.SymbolicTemporalOperator):
                expr = cast(cpt.SymbolicTemporalOperator, expr)
                lb = interval_constraint_to_smt(expr.interval.lb, constr_cache)
                ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)

                # Special case for F[0,0] phi and F[1,1] phi -- no need for quantifier
                # This is necessary for performance reasons, many FRET formulas timeout without this optimization
                if lb == "0" and ub == "0":
                    return f"({fun_signature} (or (<= len k) ({expr_map[expr.children[0]]} k len)))"
                elif lb == "1" and ub == "1":
                    return f"({fun_signature} (or (<= len (+ 1 k)) ({expr_map[expr.children[0]]} (+ 1 k) len)))"

                result = f"(assert (<= {lb} {ub}))\n"
            else: 
                expr = cast(cpt.TemporalOperator, expr)
                lb = expr.interval.lb
                ub = expr.interval.ub

                if lb == 0 and ub == 0:
                    return f"({fun_signature} (or (<= len k) ({expr_map[expr.children[0]]} k len)))"
                elif lb == 1 and ub == 1:
                    return f"({fun_signature} (or (<= len (+ 1 k)) ({expr_map[expr.children[0]]} (+ 1 k) len)))"

            return result + f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) ({expr_map[expr.children[0]]} i len)))))"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            # pi,k |= p U[lb,ub] q iff there exists i such that lb+k <= i <= ub+k and 
            #   pi,i |= q and for all j such that lb+k <= j < i it holds that pi,j |= p
            result = ""
            if isinstance(expr, cpt.SymbolicTemporalOperator):
                expr = cast(cpt.SymbolicTemporalOperator, expr)
                lb = interval_constraint_to_smt(expr.interval.lb, constr_cache)
                ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)
                result = f"(assert (<= {lb} {ub}))\n"
            else: 
                expr = cast(cpt.TemporalOperator, expr)
                lb = expr.interval.lb
                ub = expr.interval.ub

            return result + f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) ({expr_map[expr.children[1]]} i len) (forall ((j Int)) (=> (and (<= (+ {lb} k) j) (< j i)) ({expr_map[expr.children[0]]} j len)))))))"
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            # pi,k |= p R[lb,ub] q iff for all i such that lb+k <= i <= ub+k it holds that
            #   pi,i |= q or there exists j such that lb+k <= j < i it holds that pi,j |= p
            result = ""
            if isinstance(expr, cpt.SymbolicTemporalOperator):
                expr = cast(cpt.SymbolicTemporalOperator, expr)
                lb = interval_constraint_to_smt(expr.interval.lb, constr_cache)
                ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)
                result = f"(assert (<= {lb} {ub}))\n"
            else: 
                expr = cast(cpt.TemporalOperator, expr)
                lb = expr.interval.lb
                ub = expr.interval.ub

            return result + f"({fun_signature} (or (<= len (+ {lb} k)) (forall ((i Int)) (=> (and (<= (+ {lb} k) i) (<= i (+ {ub} k))) (or ({expr_map[expr.children[1]]} i len) (exists ((j Int)) (and (<= (+ {lb} k) j) (< j i) ({expr_map[expr.children[0]]} j len))))))))"
        else:
            log.error(f"unsupported expression {expr}")
            status = False
            return ""

    def expr_to_cplen(
        expr_: cpt.Expression,
        constr_cache: dict[cpt.Expression, str],
        cplen_cache: dict[cpt.Expression, str],
    ) -> str:
        """cplen(phi) is the computation length of phi:

        - cplen(p) = 1
        - cplen(! phi) = cplen(phi)
        - cplen(phi and psi) = max(cplen(phi), cplen(psi))
        - cplen(F[lb,ub] phi) = cplen(phi) + ub
        - cplen(phi U[lb,ub] psi) = max(cplen(phi) - 1, cplen(psi)) + ub
        """
        nonlocal has_mission_time
        nonlocal status

        if has_mission_time:
            cplen = "(+ M 1)"
            return cplen

        for expr in cpt.postorder(expr_, context):
            if expr in cplen_cache:
                return cplen_cache[expr]

            if isinstance(expr, cpt.Atomic):
                cplen = cplen_cache[expr.children[0]]
            elif isinstance(expr, cpt.Constant):
                cplen = "1"
            elif isinstance(expr, (cpt.Signal, cpt.Variable)):
                cplen = "1"
            elif cpt.is_arithmetic_operator(expr):
                cplen = "1"
            elif cpt.is_relational_operator(expr):
                cplen = "1"
            elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
                cplen = cplen_cache[expr.children[0]]
            elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
                cplen = smt_max_expr(cplen_cache[expr.children[0]], cplen_cache[expr.children[1]])
            elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
                cplen = smt_max_expr(cplen_cache[expr.children[0]], cplen_cache[expr.children[1]])
            elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
                cplen = smt_max_expr(cplen_cache[expr.children[0]], cplen_cache[expr.children[1]])
            elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
                cplen = smt_max_expr(cplen_cache[expr.children[0]], cplen_cache[expr.children[1]])
            elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
                if isinstance(expr, cpt.SymbolicTemporalOperator):
                    expr = cast(cpt.SymbolicTemporalOperator, expr)
                    ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)
                else: 
                    expr = cast(cpt.TemporalOperator, expr)
                    ub = expr.interval.ub
                cplen = f"(+ {cplen_cache[expr.children[0]]} {ub})"
            elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
                if isinstance(expr, cpt.SymbolicTemporalOperator):
                    expr = cast(cpt.SymbolicTemporalOperator, expr)
                    ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)
                else: 
                    expr = cast(cpt.TemporalOperator, expr)
                    ub = expr.interval.ub
                cplen = f'(+ {cplen_cache[expr.children[0]]} {ub})'
            elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
                if isinstance(expr, cpt.SymbolicTemporalOperator):
                    expr = cast(cpt.SymbolicTemporalOperator, expr)
                    ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)
                else: 
                    expr = cast(cpt.TemporalOperator, expr)
                    ub = expr.interval.ub
                cplen = f"(+ (ite (> (- {cplen_cache[expr.children[0]]} 1) {cplen_cache[expr.children[1]]}) {cplen_cache[expr.children[0]]} {cplen_cache[expr.children[1]]}) {ub})"
            elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
                if isinstance(expr, cpt.SymbolicTemporalOperator):
                    expr = cast(cpt.SymbolicTemporalOperator, expr)
                    ub = interval_constraint_to_smt(expr.interval.ub, constr_cache)
                else: 
                    expr = cast(cpt.TemporalOperator, expr)
                    ub = expr.interval.ub
                cplen = f"(+ (ite (> (- {cplen_cache[expr.children[0]]} 1) {cplen_cache[expr.children[1]]}) {cplen_cache[expr.children[0]]} {cplen_cache[expr.children[1]]}) {ub})"
            else:
                log.error(f"unsupported expression {expr}")   
                status = False
                return ""

            cplen_cache[expr] = cplen

        return cplen_cache[expr_]

    smt_commands: list[str] = [PREAMBLE]

    smt_commands.append("(set-logic UFLIA)")
    smt_commands.append("(declare-fun M () Int)")
    smt_commands.append("(assert (>= M 0))")

    # Declare symbolic interval variables and constraints on them
    for bound in context.bounds:
        smt_commands.append(f"(declare-fun {bound.symbol} () Int)")
        smt_commands.append(f"(assert (>= {bound.symbol} 0))")

    constr_cache: dict[cpt.Expression, str] = {}
    for constraint in context.constraints:
        smt_commands.append(f"(assert {interval_constraint_to_smt(constraint, constr_cache)})")

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        if typ != types.BoolType() and typ != types.IntType():
            log.error(f"unsupported type '{typ}' ({signal})")
            return ""
        atomic_map[signal] = f"f_{signal}"
        smt_commands.append(f"(declare-fun f_{signal} (Int) {to_smt_type(typ)})")

    for variable, typ in context.variables.items():
        if typ != types.BoolType() and typ != types.IntType():
            log.error(f"unsupported type '{typ}' ({variable})")
            return ""
        atomic_map[variable] = f"p_{variable}"
        smt_commands.append(f"(declare-fun p_{variable} (Int) {to_smt_type(typ)})")

    expr_map: dict[cpt.Expression, str] = {}
    expr_cache: dict[str, cpt.Expression] = {}
    cnt = 0
    for expr in cpt.postorder(start, context):
        if expr in expr_cache:
            continue
        smt_expr = expr_to_smt(expr, cnt, expr_map, expr_cache, constr_cache)
        if smt_expr == "":
            continue
        smt_commands.append(smt_expr)
        cnt += 1

    if not strict:
        cplen_cache: dict[cpt.Expression, str] = {}
        cplen = expr_to_cplen(start, constr_cache, cplen_cache)
        smt_commands.append(f"(define-fun cplen () Int {cplen})")
        smt_commands.append(f"(assert ({expr_map[start]} 0 cplen))")
    else:
        smt_commands.append("(declare-fun len () Int)")
        smt_commands.append(f"(assert ({expr_map[start]} 0 len))")

    if not status:
        return None

    smt_commands.append("(check-sat)")

    if is_nonlinear:
        log.warning("nonlinear arithmetic detected, setting logic to UFNIA")
        smt_commands[1] = "(set-logic UFNIA)"

    smt = "\n".join(smt_commands)

    return smt

def to_smt(
    expr: cpt.Expression,
    context: cpt.Context,
    theory: SMTTheory,
    strict: bool,
) -> Optional[str]:
    """Encodes the given expression into an SMT encoding and returns it. Returns None if the encoding fails."""
    log.debug(2, f"encoding expression:\n\t{repr(expr)}")

    start = util.get_rusage_time()
    if theory == SMTTheory.UFLIA:
        smt = to_uflia_smtlib2(expr, context, strict)
    elif theory == SMTTheory.QF_UFLIA:
        smt = to_qf_uflia_smtlib2(expr, context, strict)
    elif theory == SMTTheory.QF_BV:
        smt = to_qf_bv_smtlib2(expr, context, strict)
    else:
        log.error(f"unsupported SMT theory {theory}")
        return None

    end = util.get_rusage_time()
    encoding_time = end - start
    context.stats.smt_encoding_time += encoding_time

    return smt

def write_smt_encoding(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Writes the SMT encoding for the program to the given file.
    
    `options` is a dictionary of options for the writing.
    - `location`: The path to write the SMT encoding to
    - `theory`: The SMT theory to use
    - `strict`: Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.
    - `formula`: The formula to write the SMT encoding for. If not provided, all formulas will be written

    Returns:
        a ReturnCode.SUCCESS if the encoding was written successfully, ReturnCode.ERROR otherwise
    """
    def write_smt(
        formula: cpt.Formula,
        theory: SMTTheory,
        location: pathlib.Path,
        output_is_dir: bool,
        strict: bool,
    ) -> command.ReturnCode:
        smt_encoding = to_smt(formula.get_expr(), context, theory, strict)
        if smt_encoding is None:
            log.error(f"failed to write SMT encoding for {formula.symbol}", formula.loc)
            return command.ReturnCode.ERROR
        smt_path = location / f"{formula.symbol}.smt2" if output_is_dir else location
        with open(smt_path, "w") as f:
            f.write(smt_encoding)
        return command.ReturnCode.SUCCESS

    # Setup the output location
    # If the location is a file, we will overwrite it
    # If the location is a directory and already exists, we will write the encodings to it
    # If we only have one encoding and the location is not a directory, we will write it to the location as a file
    location = pathlib.Path(options["location"])
    output_is_dir = False
    if location.is_file():
        location.unlink()
    elif location.is_dir():
        output_is_dir = True

    theory = SMTTheory(options["theory"])

    if options["formula"] is not None:
        formula = program.get_spec(options["formula"])
        if formula is None:
            log.error(f"formula '{options['formula']}' not found")
            return command.ReturnCode.ERROR
        elif isinstance(formula, cpt.Contract):
            log.error(f"formula '{options['formula']}' is a contract")
            return command.ReturnCode.ERROR
        return write_smt(formula, theory, location, output_is_dir, options["strict"])

    if len(program.ft_spec_set.get_specs()) > 1:
        output_is_dir = True

    if output_is_dir:
        location.mkdir(parents=True, exist_ok=True)

    for formula in program.ft_spec_set.get_specs():
        if isinstance(formula, cpt.Contract):
            log.debug(2, f"found contract '{formula.symbol}', skipping")
            continue
        result = write_smt(formula, theory, location, output_is_dir, options["strict"])
        if result != command.ReturnCode.SUCCESS:
            return result

    return command.ReturnCode.SUCCESS

write_smt_encoding_command = command.Command(
    name="write_smt_encoding",
    description="Write the SMT encoding for the program or formula to the given location",
    options=[{
        "name": "location",
        "description": "The path to write the SMT encoding to",
        "required": True,
        "type": str,
        "default": None,
        "choices": None
    }, {
        "name": "theory",
        "description": "The SMT theory to use",
        "required": True,
        "type": str,
        "default": None,
        "choices": [member.value for member in SMTTheory]
    }, {
        "name": "strict",
        "description": "Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.",
        "required": False,
        "type": bool,
        "default": False,
        "choices": None
    }, {
        "name": "formula",
        "description": "The formula to write the SMT encoding for. If not provided, all formulas will be written",
        "required": False,
        "type": str,
        "default": None,
        "choices": None
    }],
    func=write_smt_encoding,
    guards=[command.DESUGARED],
)
command.CommandRegistry.register(write_smt_encoding_command)

def check_sat(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Checks the satisfiability of the program using the SMT encoding.
    
    `options` is a dictionary of options for the checking.
    - `theory`: The SMT theory to use
    - `strict`: Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.
    - `print`: Whether to print the results of the satisfiability checks. If not provided, unsat and unknown results will be sent as warnings.
    - `smt_max_time`: The maximum time to allow for the SMT solver in seconds
    - `smt_max_memory`: The maximum memory to allow for the SMT solver in MB, use 0 for no maximum

    Returns:
        a ReturnCode.SUCCESS if the satisfiability was checked successfully, ReturnCode.ERROR otherwise

    TODO: Add back incremental encoding support for strict encoding
    """
    theory = SMTTheory(options["theory"]) # We have to cast to SMTTheory since the command parser will return a string

    status = True
    exprs = []
    for spec in program.get_specs():
        if isinstance(spec, cpt.Contract):
            log.warning("found contract, skipping")
            continue
        log.debug(2, f"encoding SAT for '{spec.symbol}'")

        expr = spec.get_expr()
        exprs.append(expr)

        sat_smt_encoding = to_smt(expr, context, theory, options["strict"])
        if sat_smt_encoding is None:
            log.error("failed to generate SMT encoding for specification", spec.loc)
            return command.ReturnCode.ERROR
        result = run_smt_solver(
            sat_smt_encoding,
            theory,
            options["smt_max_time"],
            options["smt_max_memory"],
            context.stats,
        )
        status = status and check_sat_result(result)
        spec_str_reference = cpt.get_spec_str_reference(spec)

        log.debug(2, f"specification '{spec_str_reference}' is {result.value}")

        if not check_sat_result(result):
            log.error(f"unexpected result from SMT solver for specification '{spec_str_reference}': {result}")
            return command.ReturnCode.ERROR
        elif not options["print"] and result in [SatResult.UNSAT, SatResult.UNKNOWN]:
            log.warning(f"specification '{spec_str_reference}' is {result.value}")
            continue
        elif options["print"]:
            print(f"{spec_str_reference} : {result.value}")

    # we only check the conjunction of all specifications if there are more than one
    if len(exprs) <= 1:
        return command.ReturnCode.SUCCESS if status else command.ReturnCode.ERROR

    formula = cpt.Operator.LogicalAnd(program.loc, exprs, set_parents=False)
    sat_smt_encoding = to_smt(formula, context, theory, options["strict"])
    if sat_smt_encoding is None:
        log.error("failed to generate SMT encoding for program", program.loc)
        return command.ReturnCode.ERROR

    result = run_smt_solver(
        sat_smt_encoding,
        theory,
        options["smt_max_time"],
        options["smt_max_memory"],
        context.stats,
    )
    status = status and check_sat_result(result)

    log.debug(2, f"program is {result.value}")

    if not check_sat_result(result):
        log.error(f"unexpected result from SMT solver for program: {result}")
    elif not options["print"] and result in [SatResult.UNSAT, SatResult.UNKNOWN]:
        log.warning(f"program is {result.value}")
    elif options["print"]:
        print(f"program : {result.value}")

    return command.ReturnCode.SUCCESS if status else command.ReturnCode.ERROR

check_sat_command = command.Command(
    name="check_sat",
    description="Check the satisfiability of the program using the SMT encoding",
    options=[{
        "name": "theory",
        "description": "The SMT theory to use",
        "required": True,
        "type": str,
        "default": None,
        "choices": [member.value for member in SMTTheory]
    }, {
        "name": "strict",
        "description": "Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.",
        "required": False,
        "type": bool,
        "default": False,
        "choices": None
    }, {
        "name": "print",
        "description": "Whether to print the results of the satisfiability checks. If not provided, unsat and unknown results will be sent as warnings.",
        "required": False,
        "type": bool,
        "default": False,
        "choices": None
    }, {
        "name": "smt-max-time",
        "description": "The maximum time to allow for the SMT solver in seconds",
        "required": False,
        "type": int,
        "default": 5,
        "choices": None
    }, {
        "name": "smt-max-memory",
        "description": "The maximum memory to allow for the SMT solver in MB, use 0 for no maximum",
        "required": False,
        "type": int,
        "default": 0,
        "choices": None
    }],
    func=check_sat,
    guards=[command.DESUGARED],
)
command.CommandRegistry.register(check_sat_command)

def to_smt_equiv(
    expr1: cpt.Expression,
    expr2: cpt.Expression,
    context: cpt.Context,
    theory: SMTTheory,
    strict: bool,
) -> Optional[str]:
    log.debug(
        1, f"encoding equivalence SMT encoding for:\n\t{repr(expr1)}\n\t\t<->\n\t{repr(expr2)}",
    )

    neg_equiv_expr = cpt.Operator.LogicalNegate(
        expr1.loc,
        cpt.Operator.LogicalIff(expr1.loc, expr1, expr2, set_parents=False),
        set_parents=False,
    )

    return to_smt(neg_equiv_expr, context, theory, strict)

def write_equiv_smt(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Writes the SMT encoding for the equivalence of all formulas in the program to the given file.

    `options` is a dictionary of options for the writing.
    - `location`: The path to write the SMT encoding(s) to
    - `theory`: The SMT theory to use
    - `strict`: Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.

    Returns:
        a ReturnCode.SUCCESS if the encoding was written successfully, ReturnCode.ERROR otherwise
    """
    # Setup the output location
    # If the location is a file, we will overwrite it
    # If the location is a directory and already exists, we will write the encodings to it
    # If we only have one encoding and the location is not a directory, we will write it to the location as a file
    location = pathlib.Path(options["location"])
    output_is_dir = False
    if location.is_file():
        location.unlink()
    elif location.is_dir():
        output_is_dir = True

    theory = SMTTheory(options["theory"])

    if len(program.ft_spec_set.get_specs()) == 1:
        log.warning("only one formula in the program, nothing to do")
        return command.ReturnCode.SUCCESS

    if len(program.ft_spec_set.get_specs()) > 2:
        output_is_dir = True

    if output_is_dir:
        location.mkdir(parents=True, exist_ok=True) 

    for formula1, formula2 in zip(program.ft_spec_set.get_specs(), program.ft_spec_set.get_specs()[1:]):
        if isinstance(formula1, cpt.Contract):
            log.debug(2, f"found contract '{formula1.symbol}', skipping")
            continue
        if isinstance(formula2, cpt.Contract):
            log.debug(2, f"found contract '{formula2.symbol}', skipping")
            continue

        equiv_smt = to_smt_equiv(formula1.get_expr(), formula2.get_expr(), context, theory, options["strict"])
        if not equiv_smt:
            log.error("failed to generate SMT encoding for equivalence", formula1.loc)
            return command.ReturnCode.ERROR

        smt_path = location / f"equiv_{formula1.symbol}_{formula2.symbol}.smt2" if output_is_dir else location
        with open(smt_path, "w") as f:
            f.write(equiv_smt)

    return command.ReturnCode.SUCCESS

write_equiv_smt_command = command.Command(
    name="write_equiv_smt_encoding",
    description="Write the SMT encoding(s) for the equivalence of all formulas in the program to the given location. If there are more than two formulas, the encodings will be written to a directory.",
    options=[{
        "name": "location",
        "description": "The path to write the SMT encoding(s) to",
        "required": True,
        "type": str,
        "default": None,
        "choices": None
    }, {
        "name": "theory",
        "description": "The SMT theory to use",
        "required": True,
        "type": str,
        "default": None,
        "choices": [member.value for member in SMTTheory]
    }, {
        "name": "strict",
        "description": "Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.",
        "required": False,
        "type": bool,
        "default": False,
        "choices": None
    }],
    func=write_equiv_smt,
    guards=[command.DESUGARED],
)
command.CommandRegistry.register(write_equiv_smt_command)

def check_equiv(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Checks that all formulas in the program are equivalent.
    
    `options` is a dictionary of options for the checking.
    - `theory`: The SMT theory to use
    - `strict`: Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.
    - `quiet`: Whether to print the results of the equivalence checks.
    - `smt_max_time`: The maximum time to allow for the SMT solver in seconds
    - `smt_max_memory`: The maximum memory to allow for the SMT solver in MB, use 0 for no maximum

    Returns:
        a ReturnCode.SUCCESS if the equivalence was checked successfully, ReturnCode.ERROR otherwise
    """
    class EquivResult(enum.Enum):
        EQUIV = "equiv"
        NOT_EQUIV = "not-equiv"
        UNKNOWN = "unknown"

    status = True
    equiv = EquivResult.EQUIV
    theory = SMTTheory(options["theory"]) # We have to cast to SMTTheory since the command parser will return a string

    for spec1, spec2 in zip(program.get_specs(), program.get_specs()[1:]):
        if isinstance(spec1, cpt.Contract):
            log.warning("found contract, skipping")
            continue

        if isinstance(spec2, cpt.Contract):
            log.warning("found contract, skipping")
            continue

        log.debug(2, f"checking equivalence of '{cpt.get_spec_str_reference(spec1)}' and '{cpt.get_spec_str_reference(spec2)}'")

        expr1 = spec1.get_expr()
        expr2 = spec2.get_expr()
        equiv_smt = to_smt_equiv(expr1, expr2, context, theory, options["strict"])
        if equiv_smt is None:
            log.error("failed to generate SMT encoding for equivalence", spec1.loc)
            status = False
            continue

        result = run_smt_solver(
            equiv_smt,
            theory,
            options["smt_max_time"],
            options["smt_max_memory"],
            context.stats,
        )
        status = status and check_sat_result(result)
        spec_str_reference = f"{cpt.get_spec_str_reference(spec1)} = {cpt.get_spec_str_reference(spec2)}"

        if result == SatResult.SAT:
            equiv = EquivResult.NOT_EQUIV
            log.debug(2, f"'{spec_str_reference}' does not hold")
        elif result == SatResult.UNSAT:
            log.debug(2, f"'{spec_str_reference}' holds")
        else:
            equiv = equiv if equiv == EquivResult.NOT_EQUIV else EquivResult.UNKNOWN
            log.debug(2, f"'{spec_str_reference}' is unknown")

    if not options["quiet"]:
        print(equiv.value)

    return command.ReturnCode.SUCCESS if status else command.ReturnCode.ERROR

check_equiv_command = command.Command(
    name="check_equiv",
    description="Check that all formulas in the program are equivalent using the SMT encoding",
    options=[{
        "name": "theory",
        "description": "The SMT theory to use",
        "required": True,
        "type": str,
        "default": None,
        "choices": [member.value for member in SMTTheory]
    }, 
    {
        "name": "strict",
        "description": "Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.",
        "required": False,
        "type": bool,
        "default": False,
        "choices": None
    },
    {
        "name": "quiet",
        "description": "Whether to print the results of the equivalence checks.",
        "required": False,
        "type": bool,
        "default": False,
        "choices": None
    },
    {
        "name": "smt-max-time",
        "description": "The maximum time to allow for the SMT solver in seconds",
        "required": False,
        "type": int,
        "default": 5,
        "choices": None
    }, {
        "name": "smt-max-memory",
        "description": "The maximum memory to allow for the SMT solver in MB, use 0 for no maximum",
        "required": False,
        "type": int,
        "default": 0,
        "choices": None
    }],
    func=check_equiv,
    guards=[command.DESUGARED],
)   
command.CommandRegistry.register(check_equiv_command)
