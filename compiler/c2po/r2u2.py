from typing import Any, Optional
import pathlib
import shutil
import subprocess
import statistics
from c2po import cpt, log, util, command

def find_r2u2_executable() -> Optional[pathlib.Path]:
    """
    Find the R2U2 executable by checking PATH first, then compiler/../monitors/c/build/r2u2.

    Returns:
        The path to the R2U2 executable if found, otherwise returns None.
    """
    r2u2_in_path = shutil.which("r2u2")
    if r2u2_in_path is not None and util.check_executable(r2u2_in_path):
        return pathlib.Path(r2u2_in_path)
    r2u2_in_compiler = util.C2PO_SRC_DIR / ".." / ".." / "monitors" / "c" / "build" / "r2u2"
    if util.check_executable(str(r2u2_in_compiler)):
        return r2u2_in_compiler
    return None

def run_r2u2(program: cpt.Program, context: cpt.Context, options: dict[str, Any]):
    """
    Run R2U2 on a given specification and trace file.

    `options` is a dictionary of options for the running.
    - `binary`: The filename for the spec binary
    - `trace`: The filename of the trace to run over
    - `num-runs`: The number of times to run R2U2. If more than 1, the latest output will be printed and written to the output file. The reported time will be the median of the runs.
    - `print`: Whether to print the R2U2 output to the console.
    - `output`: The filename to write the R2U2 output to.
    - `r2u2dir`: The directory to run R2U2 in.

    Returns:
        a ReturnCode.SUCCESS if the R2U2 was run successfully, ReturnCode.ERROR otherwise
    """
    spec_binary = options["binary"]
    trace = options["trace"]
    print_output = options["print"]
    output_file = options["output"]
    num_runs = options["num_runs"]
    r2u2_dir = options["r2u2dir"]

    if r2u2_dir != "" and r2u2_dir is not None:
        r2u2_executable = pathlib.Path(r2u2_dir) / "build" / "r2u2"
        if not r2u2_executable.exists():
            log.error(f"R2U2 executable not found at {r2u2_executable}")
            context.stats.r2u2_status = "error"
            return command.ReturnCode.ERROR
    else:
        r2u2_executable = find_r2u2_executable()
        if r2u2_executable is None:
            log.error("could not find R2U2 executable")
            context.stats.r2u2_status = "error"
            return command.ReturnCode.ERROR

    command_ = [str(r2u2_executable), str(spec_binary), str(trace)]
    runtimes = []
    output = b""
    for i in range(max(num_runs, 1)):
        log.debug(1, f"running R2U2 {i + 1} of {num_runs}...")
        log.debug(1, f"command: {command_}")

        start_time = util.get_children_rusage_time()
        proc = subprocess.run(
            command_,
            capture_output=True
        )
        end_time = util.get_children_rusage_time()
        elapsed = end_time - start_time
        log.debug(1, f"R2U2 {i + 1} of {num_runs} completed in {elapsed} seconds")
        runtimes.append(elapsed)
        output = proc.stdout
        if proc.returncode != 0:
            log.error(f"R2U2 returned with code {proc.returncode}")
            log.error(output.decode("utf-8").strip())
            log.error(proc.stderr.decode("utf-8").strip())
            context.stats.r2u2_status = "error"
            return command.ReturnCode.ERROR

    context.stats.r2u2_median_runtime = statistics.median(runtimes)
    context.stats.r2u2_average_runtime = statistics.mean(runtimes)
    context.stats.r2u2_min_runtime = min(runtimes)
    context.stats.r2u2_max_runtime = max(runtimes)

    context.stats.r2u2_status = "ok"
    if print_output:
        print(output.decode("utf-8").strip())
    if output_file is not None:
        with open(output_file, "wb") as f:
            f.write(output)

    return command.ReturnCode.SUCCESS

run_r2u2_command = command.Command(
    name="run_r2u2",
    description="Run R2U2 over the trace attached to the context using the assembly attached to the context.",
    func=run_r2u2,
    options=[
        {
            "name": "binary",
            "description": "The filename for the spec binary.",
            "required": True,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "trace",
            "description": "The filename of the trace to run over.",
            "required": True,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "num-runs",
            "description": "The number of times to run R2U2.",
            "required": False,
            "type": int,
            "default": 1,
            "choices": None,
        },
        {
            "name": "print",
            "description": "Print the R2U2 output to the console.",
            "required": False,
            "type": bool,
            "default": False,
            "choices": None,
        },
        {
            "name": "output",
            "description": "The filename to write the R2U2 output to.",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "r2u2dir",
            "description": "The directory to run R2U2 in.",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        },
    ],
    guards=[command.ASSEMBLED]
)
command.CommandRegistry.register(run_r2u2_command)
