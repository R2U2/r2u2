from __future__ import annotations
import code 
import sys
import pathlib
import tempfile
import os
import shlex
from typing import Optional
from types import ModuleType
from c2po import (
    cpt,
    log,
    type_check,
    transform,
    eqsat, # noqa: F401
    sat, # noqa: F401
    atomics,
    cse,
    desugar,
    scq,
    assemble,
    rewrite,
    command,
    serialize, # noqa: F401 
    parse_c2po,
    parse_mltl, # noqa: F401
    parse_equiv, # noqa: F401
    util,
    r2u2, # noqa: F401
    trace, # noqa: F401
    map, # noqa: F401
    sabre, # noqa: F401
)

# Try and import readline for better REPL experience
readline: Optional[ModuleType]
try:
    import readline
except ImportError:
    readline = None

C2PO_RC_PATH = util.C2PO_SRC_DIR.parent / ".c2porc"

sys.ps1 = "c2po> "
sys.ps2 = "    "

compile_command = command.CompositeCommand(
    name="compile",
    description="Compile a program after parsing with basic optimizations. No dependencies on external tools.",
    commands=[
        type_check.type_check_command,
        desugar.desugar_command,
        rewrite.optimize_rewrites_command,
        transform.remove_extended_operators_command,
        transform.multi_operators_to_binary_command,
        cse.optimize_cse_command,
        assemble.assemble_command,
    ],
    guards=[]
)
command.CommandRegistry.register(compile_command)

# A dictionary of failed guard conditions to the command that will likely fix them
FAILED_GUARD_SUGGESTIONS: dict[command.CommandGuard, list[command.Command]] = {
    command.VALID_PROGRAM: [parse_c2po.parse_c2po_command, parse_mltl.parse_mltl_command],
    command.VALID_SIGNAL_MAPPING: [map.parse_map_command, map.generate_map_command, trace.parse_trace_command, parse_mltl.parse_mltl_command],
    command.WELL_TYPED: [type_check.type_check_command],
    command.DESUGARED: [desugar.desugar_command],
    command.VALID_SCQ_SIZES: [scq.compute_scq_sizes_command],
    command.COMPUTED_ATOMICS: [atomics.compute_atomics_command],
    command.ONLY_BINARY_OPERATORS: [transform.multi_operators_to_binary_command],
    command.NO_EXTENDED_OPERATORS: [transform.remove_extended_operators_command],
    command.ASSEMBLED: [assemble.assemble_command],
}

def print_failed_guard_message(failed_guard: command.CommandGuard, cur_command: command.Command) -> None:
    """Prints a message for a failed guard condition."""
    if failed_guard in FAILED_GUARD_SUGGESTIONS:
        failed_guard_suggestions = FAILED_GUARD_SUGGESTIONS[failed_guard]
        failed_guard_suggestion_names = [
            suggestion.name for suggestion in failed_guard_suggestions
        ]
        log.error(
            f"guard condition not met for {cur_command.name}: {failed_guard.name}\n"
            + f"    consider trying one of the following commands: {', '.join(failed_guard_suggestion_names)}"
        )
    else:
        log.error(f"guard condition not met for {cur_command.name}: {failed_guard.name}")

class CommandConsole(code.InteractiveConsole):
    """Interactive console that supports custom Commands.

    This class extends code.InteractiveConsole to handle custom commands (as defined
    in command.py). Commands are checked first and executed if found.
    """
    
    def __init__(self, filename: str = "<console>"):
        """Initialize the CommandConsole with a list of Commands.
        
        Args:
            filename: Optional filename for error reporting
        """
        super().__init__(filename=filename)
        self.program: cpt.Program = cpt.Program.dummy()
        self.context: cpt.Context = cpt.Context()
        self.commands = command.CommandRegistry.commands
        self.command_dict = {command.name: command for command in self.commands}
        self.return_code = command.ReturnCode.SUCCESS
        self.state_stack: list[tuple[cpt.Program, cpt.Context]] = []

    def runsource(self, source: str, filename: str = "<input>", symbol: str = "single") -> bool:
        """Execute a source string, checking for commands first, then falling back to Python execution.
        
        Args:
            source: The command to execute 
            filename: The filename for error reporting
            symbol: The symbol type ('single' for single statement, 'exec' for compound)
        
        Returns:
            True if the input was incomplete (needs more input), False otherwise
        """
        source = source.strip()
        
        # Ignore empty lines and comments
        if source == "" or source.startswith("#"):
            return False

        try:
            parts = shlex.split(source)
            command_name = parts[0] if parts else ""
            command_args = parts[1:] if len(parts) > 1 else []
        except ValueError:
            log.error("error parsing command")
            self.set_return_code(command.ReturnCode.SHLEX_ERROR)
            return False

        if command_name == "exit":
            sys.exit(self.return_code.value)
        elif command_name == "push":
            self.push_state()
            return False
        elif command_name == "pop":
            if len(self.state_stack) == 0:
                log.error("no state to pop, use 'push' to create a new state")
                self.set_return_code(command.ReturnCode.NO_STATE_TO_POP)
                return False
            self.pop_state()
            return False
        elif command_name not in self.command_dict:
            log.error(f"unknown command: {command_name}\nUse 'help' to see all available commands.")
            self.set_return_code(command.ReturnCode.UNKNOWN_COMMAND)
            return False

        cur_command = self.command_dict[command_name]

        try:
            # Parse the command arguments (for validation and --help) and add the global options
            options = cur_command.parse_args(command_args)

            failed_guard = cur_command.check_guards(self.program, self.context)
            if failed_guard is None:
                result = cur_command.execute(self.program, self.context, options)
            else:
                print_failed_guard_message(failed_guard, cur_command)
                self.set_return_code(command.ReturnCode.GUARD_CONDITION_NOT_MET)
                return False

            # Parse functions return a program or None, all other functions return a ReturnCode
            if isinstance(result, cpt.Program):
                self.program = result
                self.set_return_code(command.ReturnCode.SUCCESS)
            elif result is None: # parse functions return None on error
                self.set_return_code(command.ReturnCode.PARSE_ERROR)
            elif isinstance(result, tuple): 
                # Commands return the failed command and guard condition on error
                print_failed_guard_message(result[1], result[0])
                self.set_return_code(command.ReturnCode.GUARD_CONDITION_NOT_MET)
            elif isinstance(result, command.ReturnCode):
                self.set_return_code(result)
            else:
                log.internal(f"'{command_name}' returned unexpected result type {type(result)}")
                self.set_return_code(command.ReturnCode.UNKNOWN_RESULT_TYPE)

        except SystemExit:
            # argparse calls sys.exit() on --help or errors, catch it
            self.set_return_code(command.ReturnCode.ARGPARSE_EXIT)
            return False

        return False

    def set_return_code(self, return_code: command.ReturnCode) -> None:
        """Sets the return code to the given return code if the given return code is an error."""
        if return_code.is_error():
            self.return_code = return_code

    def push_state(self) -> None:
        """Push the current state onto the state stack."""
        self.state_stack.append(cpt.deepcopy_program_with_context(self.program, self.context))

    def pop_state(self) -> None:
        """Pop the current state from the state stack."""
        self.program, self.context = self.state_stack.pop()


def run_rc_script(console: CommandConsole) -> None:
    """Runs the given RC script file."""
    with open(C2PO_RC_PATH, "r") as file:
        for line in file:
            line = line.strip()
            console.runsource(line)


def interactive() -> command.ReturnCode:
    """Start an interactive REPL loop using the code library.
    
    This function creates an interactive console that waits for user input
    and executes commands in a REPL loop.
    """
    console = CommandConsole()
    if C2PO_RC_PATH.exists():
        run_rc_script(console)
    console.interact(banner="C2PO Interactive REPL (type 'exit', 'quit', or Ctrl-D to quit)", exitmsg="")
    return console.return_code

def script(script_filename: str, chdir: bool = True) -> command.ReturnCode:
    """Execute REPL commands from a script file using the code library.
    
    This function reads commands from script_filename, executes them in a REPL context, then exits.
    """
    console = CommandConsole()
    console.context.script_filename = script_filename

    if C2PO_RC_PATH.exists():
        run_rc_script(console)

    contents = util.read_file(script_filename)
    if contents is None:
        return command.ReturnCode.FILE_NOT_FOUND

    # Set current working directory to the directory of the script file so that all paths are
    # relative to the script file
    script_path = pathlib.Path(script_filename)
    if chdir:
        os.chdir(script_path.parent)

    for line in contents.splitlines():
        console.runsource(line.strip())

    return console.return_code

def cli(
    spec_filename: str,
    trace_filename: Optional[str],
    map_filename: Optional[str],
    output_filename: Optional[str],
    write_bounds_filename: Optional[str],
    quiet: bool,
    debug: bool,
    only_parse: bool,
    only_type_check: bool,
    only_compile: bool,
    mission_time: int,
    scq_constant: int,
    enable_booleanizer: bool,
    enable_aux: bool,
    enable_cse: bool,
    enable_rewrite: bool,
    enable_extops: bool,
    enable_eqsat: bool,
    enable_eqsat_equiv_check: bool,
    enable_eqsat_const_folding: bool,
    enable_eqsat_associative: bool, 
    enable_eqsat_commutative: bool,
    enable_eqsat_multi_arity: bool,
    enable_eqsat_temporal: bool,
    eqsat_max_time: int,
    eqsat_max_memory: int,
    num_gurobi_threads: int,
    egglog_path: Optional[str],
    check_sat: bool,
    smt_theory: str,
    smt_max_time: int,
    smt_max_memory: int,
    smt_solver_path: Optional[str],
) -> command.ReturnCode:
    """Command line interface for the C2PO compiler."""
    script_lines: list[str] = []

    if enable_booleanizer:
        script_lines.append("enable_booleanizer")
    if mission_time > -1:
        script_lines.append(f"set_mission_time {mission_time}")
    if debug:
        script_lines.append("set_debug")

    spec_path = pathlib.Path(spec_filename)
    if spec_path.suffix == ".c2po":
        script_lines.append(f"parse_c2po {spec_path}")
    elif spec_path.suffix == ".mltl":
        script_lines.append(f"parse_mltl {spec_path}")
    else:
        log.error(f"invalid specification file: {spec_path}")
        return command.ReturnCode.FILE_NOT_FOUND

    if trace_filename:
        script_lines.append(f"parse_trace {trace_filename}")
    if map_filename:
        script_lines.append(f"parse_map {map_filename}")

    if only_parse:
        script_lines.append("exit")

    script_lines.append("type_check")
    if only_type_check:
        script_lines.append("exit")

    script_lines.append("desugar")
    
    if enable_eqsat:
        cmd = f"optimize_eqsat --egglog-max-time {eqsat_max_time} --egglog-max-memory {eqsat_max_memory} " \
                  f"--num-gurobi-threads {num_gurobi_threads} " \
                  f"--theory {smt_theory} --smt-max-time {smt_max_time} --smt-max-memory {smt_max_memory} " \
                  f"--{'no-' if not enable_eqsat_equiv_check else ''}check-equiv " \
                  f"--{'no-' if not enable_eqsat_const_folding else ''}const-folding " \
                  f"--{'no-' if not enable_eqsat_associative else ''}associative " \
                  f"--{'no-' if not enable_eqsat_commutative else ''}commutative " \
                  f"--{'no-' if not enable_eqsat_multi_arity else ''}multi-arity " \
                  f"--{'no-' if not enable_eqsat_temporal else ''}temporal" \
                  f"{f'--egglog-bin {egglog_path}' if egglog_path else ''} " \
                  f"{f'--smt-solver-path {smt_solver_path}' if smt_solver_path else ''}"
        script_lines.append(cmd)
    elif enable_rewrite:
        script_lines.append("optimize_rewrites")

    if not enable_extops:
        script_lines.append("remove_extended_operators")

    if enable_cse:
        script_lines.append("optimize_cse")

    if check_sat:
        script_lines.append(
            f"check_sat {smt_theory} --smt-max-time {smt_max_time} --smt-max-memory {smt_max_memory}"
        )

    if only_compile:
        script_lines.append("exit")

    script_lines.append("multi_operators_to_binary")
    script_lines.append("remove_extended_operators")

    if output_filename:
        script_lines.append(f"assemble {'--aux' if enable_aux else '--no-aux'} {'--print' if not quiet else ''} {'--scq-constant ' + str(scq_constant) if scq_constant > 0 else ''} {output_filename}")

    if write_bounds_filename:
        bounds_path = pathlib.Path(write_bounds_filename)
        if bounds_path.suffix == ".h":
            script_lines.append(f"write_bounds_c {bounds_path}")
        elif bounds_path.suffix == ".toml":
            script_lines.append(f"write_bounds_rust {bounds_path}")
        else:
            log.error(f"invalid bounds file: {bounds_path}")
            return command.ReturnCode.FILE_NOT_FOUND

    try:
        with tempfile.NamedTemporaryFile() as temp_file:
            temp_file.write("\n".join(script_lines).encode('utf-8'))
            temp_file.flush()
            return script(temp_file.name, chdir=False)
    except OSError:
        log.error("problem writing temporary script file")
        return command.ReturnCode.FILE_NOT_FOUND

def main_rs(
    spec_filename: str,
    trace_filename: str,
    map_filename: str,
    output_filename: str,
    write_bounds_filename: str,
    enable_aux: bool,
    enable_booleanizer: bool,
    enable_rewrite: bool,
    enable_cse: bool,
    enable_sat: bool,
    timeout_sat: int
):
    """
    Wrapper for main function to allow for easier interfacing with Rust CLI tool and playground. 
    
    The library used for interfacing the Python code in Rust is PyO3 and has a small limit on the
    number of arguments that can be passed (~10), so we wrap the main function in a wrapper and pass
    in default values for the arguments that are not needed. These arguments are not able to be used
    in the Rust CLI tool and playground as a result.
    """
    return cli(
        spec_filename=spec_filename,
        trace_filename=trace_filename if trace_filename != "" else None,
        map_filename=map_filename if map_filename != "" else None,
        output_filename=output_filename if output_filename != "" else None,
        write_bounds_filename=write_bounds_filename if write_bounds_filename != "" else None,
        enable_aux=enable_aux,
        enable_booleanizer=enable_booleanizer,
        enable_cse=enable_cse,
        check_sat=enable_sat,
        smt_max_time=timeout_sat,
        quiet=False,
        debug=False,
        only_parse=False,
        only_type_check=False,
        only_compile=False,
        mission_time=-1,
        scq_constant=0,
        enable_extops=False,
        enable_rewrite=enable_rewrite,
        enable_eqsat=False,
        enable_eqsat_equiv_check=False,
        enable_eqsat_const_folding=False,
        enable_eqsat_associative=False,
        enable_eqsat_commutative=False,
        enable_eqsat_multi_arity=False,
        enable_eqsat_temporal=False,
        eqsat_max_time=5,
        eqsat_max_memory=0,
        num_gurobi_threads=0,
        egglog_path="",
        smt_theory="uflia",
        smt_max_memory=0,
        smt_solver_path="",
    )
