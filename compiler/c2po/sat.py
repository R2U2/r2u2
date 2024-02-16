import pathlib
import shutil
import subprocess
import enum

from c2po import cpt, log

MODULE_CODE = "SAT"

WORK_DIR = pathlib.Path(__file__).parent / "__workdir__"

Z3 = "z3"

class SatResult(enum.Enum):
    SAT = 0
    UNSAT = 1
    UNKNOWN = 2


def check_sat(program: cpt.Program, context: cpt.Context) -> "dict[cpt.Specification, SatResult]":
    """Runs an SMT solver (Z3 by default) on the SMT encoding of the MLTL formulas in `program`."""
    if WORK_DIR.is_file():
        WORK_DIR.unlink()
    elif WORK_DIR.is_dir():
        shutil.rmtree(WORK_DIR)
    
    WORK_DIR.mkdir()

    results: dict[cpt.Specification, SatResult] = {}
    
    for spec in program.ft_spec_set.get_specs():
        if isinstance(spec, cpt.Contract):
            log.warning("Found contract, skipping", MODULE_CODE)
            continue
            
        expr = spec.get_expr()

        smt = cpt.to_smt_sat_query(expr, context)

        smt_file_path = WORK_DIR / f"{spec.symbol}.smt"
        with open(smt_file_path, "w") as f:
            f.write(smt)

        command = [Z3, str(smt_file_path)]
        log.debug(f"Running '{' '.join(command)}'", MODULE_CODE)
        proc = subprocess.run(command, capture_output=True)

        if proc.stdout.decode().find("unsat") > -1:
            results[spec] = SatResult.UNSAT
        elif proc.stdout.decode().find("sat") > -1:
            results[spec] = SatResult.SAT
        else:
            results[spec] = SatResult.UNKNOWN

    shutil.rmtree(WORK_DIR)
        
    return results

