from __future__ import annotations
from pathlib import Path
from typing import Dict, List, Tuple
import re

from .logger import logger, Color
from .ast import *
from .type_check import type_check
from .rewrite import *
from .optimize import *
from .parse import parse
from .assembly import generate_assembly
from .assembler import assemble

SignalMapping = Dict[str, int]

class ReturnCode(Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERR = 2
    TYPE_CHECK_ERR = 3
    ASM_ERR = 4
    INVALID_OPTIONS = 5
    FILE_IO_ERR  = 6

# COMPILE_ERR_RETURN_VAL: Callable[[int], tuple[int, List[TLInstruction], List[TLInstruction], List[BZInstruction], List[ATInstruction], List[Tuple[int,int]]]] = lambda rc: (rc,[],[],[],[],[])


# # Stores the sub-classes of Instruction from ast.py
# INSTRUCTION_LIST = [cls for (name,cls) in inspect.getmembers(sys.modules["c2po.cpt"],
#         lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction))]

# DEFAULT_CPU_LATENCY_TABLE: Dict[str, int] = { name:10 for (name,value) in
#     inspect.getmembers(sys.modules["c2po.cpt"],
#         lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction) and
#             obj != Instruction and
#             obj != TLInstruction and
#             obj != BZInstruction) }

# DEFAULT_FPGA_LATENCY_TABLE: Dict[str, Tuple[float,float]] = { name:(10.0,10.0) for (name,value) in
#     inspect.getmembers(sys.modules["c2po.cpt"],
#         lambda obj: inspect.isclass(obj) and issubclass(obj, Instruction) and
#             obj != Instruction and
#             obj != TLInstruction and
#             obj != BZInstruction) }


AT_FILTER_TABLE: Dict[str, Tuple[List[C2POType], C2POType]] = {
    "rate": ([C2POFloatType(False)], C2POFloatType(False)),
    "movavg": ([C2POFloatType(False),C2POIntType(True)], C2POFloatType(False)),
    "abs_diff_angle": ([C2POFloatType(False),C2POFloatType(True)], C2POFloatType(False))
}


def generate_aliases(program: C2POProgram, context: C2POContext) -> List[str]:
    """
    Generates strings corresponding to the alias file for the argument program. The alias file is used by R2U2 to print formula labels and contract status.

    Preconditions:
        - program is type correct

    Postconditions:
        - None
    """
    s: List[str] = []

    for spec_section in [s for s in program.get_spec_sections()]:
        for spec in [s for s in spec_section.get_specs() if isinstance(s, C2POSpecification)]:
            s.append(f"F {spec.symbol} {spec.formula_number}")

    for contract in context.contracts.values():
        (f1, f2, f3) =  contract.formula_numbers
        s.append(f"C {contract.symbol} {f1} {f2} {f3}")

    return s


def compute_scq_size(node: C2PONode) -> int:
    """
    Computes SCQ sizes for each node and returns the sum of each SCQ size. Sets this sum to the total_scq_size value of `node`.
    """
    visited: List[int] = []
    total: int = 0

    def compute_scq_size_util(node: C2PONode) :
        nonlocal visited
        nonlocal total

        if id(node) in visited:
            return
        visited.append(id(node))

        if isinstance(node, C2POSpecification):
            node.scq_size = 1
            total += node.scq_size
            return

        max_wpd: int = 0
        for p in node.get_parents():
            for s in p.get_children():
                if not id(s) == id(node):
                    max_wpd = s.wpd if s.wpd > max_wpd else max_wpd

        node.scq_size = max(max_wpd-node.bpd,0)+3 # works for +3 b/c of some bug -- ask Brian
        total += node.scq_size

    postorder(node, compute_scq_size_util)
    node.total_scq_size = total

    return total


def generate_scq_assembly(program: C2POProgram) -> List[Tuple[int,int]]:
    return []
    ret: List[Tuple[int,int]] = []
    pos: int = 0

    program.total_scq_size = compute_scq_size(program.get_ft_specs())

    def gen_scq_assembly_util(a: C2PONode) :
        nonlocal ret
        nonlocal pos

        if a.ftid < 0 or isinstance(a, C2POSpecSection):
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        ret.append((start_pos,end_pos))

    postorder(program.get_ft_specs(), gen_scq_assembly_util)
    program.scq_assembly = ret

    return ret


def compute_cpu_wcet(program: C2POProgram, latency_table: Dict[str, int], clk: int) -> int:
    """
    Compute and return worst-case execution time in clock cycles for software version R2U2 running on a CPU. Sets this total to the cpu_wcet value of program.

    latency_table is a dictionary that maps the class names of AST nodes to their estimated computation time in CPU clock cycles. For instance, one key-value pair may be ('LogicalAnd': 15). If an AST node is found that does not have a corresponding value in the table, an error is reported.

    Preconditions:
        - program has had its assembly generated

    Postconditions:
        - None
    """
    wcet: int = 0

    def compute_cpu_wcet_util(a: C2PONode) -> int:
        nonlocal latency_table

        classname: str = type(a).__name__
        if classname not in latency_table:
            logger.error(f' Operator \'{classname}\' not found in CPU latency table.')
            return 0
        else:
            return int((latency_table[classname] * a.scq_size) / clk)

    wcet = sum([compute_cpu_wcet_util(a) for a in program.assembly])
    program.cpu_wcet = wcet
    return wcet


def compute_fpga_wcet(program: C2POProgram, latency_table: Dict[str, Tuple[float, float]], clk: float) -> float:
    """
    Compute and return worst-case execution time in micro seconds for hardware version R2U2 running on an FPGA. Sets this total to the fpga_wcet value of program.

    latency_table is a dictionary that maps the class names of AST nodes to their estimated computation time in micro seconds. For instance, one key-value pair may be ('LogicalAnd': 15.0). If an AST node is found that does not have a corresponding value in the table, an error is reported.

    Preconditions:
        - program has had its assembly generated

    Postconditions:
        - None
    """
    wcet: float = 0

    def compute_fpga_wcet_util(a: C2PONode) -> float:
        nonlocal latency_table

        classname: str = type(a).__name__
        if classname not in latency_table:
            logger.error(f' Operator \'{classname}\' not found in FPGA latency table.')
            return 0
        else:
            sum_scq_sizes_children = sum([c.scq_size for c in a.get_children()])
            return latency_table[classname][0] + latency_table[classname][1]*sum_scq_sizes_children

    wcet = sum([compute_fpga_wcet_util(a) for a in program.assembly]) / clk
    program.fpga_wcet = wcet
    return wcet


def set_options(
    impl_str: str, 
    int_width: int, 
    int_is_signed: bool, 
    float_width: int,
    at: bool, 
    bz: bool, 
    extops: bool
) -> bool:
    """Checks that the options are valid for the given implementation.
    
    Args:
        program: Target program for compilation
        impl_str: String representing one of the R2U2 implementation 
            (should be one of 'c', 'c++'/'cpp', or 'fpga'/'vhdl')
        movavg_size: Maximum size for moving average AT filter
        int_width: Width to set C2PO INT type to
        int_is_signed: If true sets INT type to signed
        float_width: Width to set C2PO FLOAT type to
        enable_at: If true enables Atomic Checker instructions
        enable_bz: If true enables Booleanizer instructions
    """
    status: bool = True
    
    impl: R2U2Implementation = str_to_r2u2_implementation(impl_str)
    set_types(impl, int_width, int_is_signed, float_width)

    if bz and at:
        logger.error(f" Only one of AT and BZ can be enabled")
        status = False
    
    if impl == R2U2Implementation.C:
        if not ((not bz and at) or (bz and not at)):
            logger.error(f" Exactly one of booleanizer or atomic checker must be enabled for C implementation.")
            status = False
    else: # impl == R2U2Implementation.CPP or impl == R2U2Implementation.VHDL
        if bz:
            logger.error(f" Booleanizer only available for C implementation.")
            status = False

    if impl == R2U2Implementation.CPP or impl == R2U2Implementation.VHDL:
        if extops:
            logger.error(f" Extended operators only support for C implementation.")
            status = False

    return status


def configure_paths(
        input_filename: str, 
        trace_filename: Optional[str], 
        map_filename: Optional[str]
) -> Tuple[Optional[Path], Optional[Path], Optional[Path]]:
    """Perform file validation on each argument and return Path objects for each corresponding filename given."""
    # input file validation
    input_path = Path(input_filename)
    if not input_path.is_file():
        logger.error(f"Input file '{input_filename} not a valid file.'")
        input_path = None

    # trace file validation
    trace_path = None
    if trace_filename:
        trace_path =  Path(trace_filename)
        if not trace_path.is_file():
            logger.error(f"Trace file '{trace_filename}' is not a valid file.")

    # map file validation
    map_path = None
    if map_filename:
        map_path =  Path(map_filename)
        if not map_path.is_file():
            logger.error(f"Trace file '{map_filename}' is not a valid file.")
    
    return (input_path, trace_path, map_path)


def process_trace_file(trace_path: Path, return_mapping: bool) -> Tuple[Optional[int], Optional[SignalMapping]]:
    """Given `trace_path`, return the inferred mission time and, if `return_mapping` is enabled, a signal mapping."""
    with open(trace_path,"r") as f:
        content: str = f.read()

    lines: List[str] = content.splitlines()

    if len(lines) < 1:
        return (0, None)

    cnt: int = 0
    signal_mapping: SignalMapping = {}

    if lines[0][0] == "#":
        # then there is a header
        header = lines[0][1:]

        if return_mapping:
            logger.warning("Map file given and header included in trace file; header will be ignored.")

        for id in [s.strip() for s in header.split(",")]:
            if id in signal_mapping:
                logger.warning(f"{trace_path.name}:{1}: Signal ID '{id}' found multiple times in csv, using right-most value.")
            signal_mapping[id] = cnt
            cnt += 1

        mission_time = len(lines) - 1

        return (mission_time, signal_mapping)

    # no header, so just return number of lines in file (i.e., number of time steps in trace)
    return (len(lines), None)


def process_map_file(map_path: Path) -> Optional[SignalMapping]:
    """Given `trace_path`, return the inferred mission time and, if `return_mapping` is enabled, a signal mapping."""
    with open(map_path, "r") as f:
        content: str = f.read()

    mapping: SignalMapping = {}

    lines = content.splitlines()
    for line in lines:
        if re.match("[a-zA-Z_]\\w*:\\d+", line):
            strs = line.split(":")
            id = strs[0]
            sid = int(strs[1])

            if id in mapping:
                logger.warning(f"{map_path.name}:{lines.index(line)+1}: Signal ID '{id}' found multiple times in map file, using latest value.")

            mapping[id] = sid
        else:
            logger.error(f"{map_path.name}:{lines.index(line)}: Invalid format for map line (found {line})\n\t Should be of the form SYMBOL ':' NUMERAL")
            return None

    return None


def assign_signal_ids(program: C2POProgram, mapping: SignalMapping):

    def assign_signal_ids_util(node: C2PONode):
        if isinstance(node, C2POSignal):
            if node.symbol not in mapping:
                logger.error(f"Mapping does not contain signal '{node.symbol}'.")
                return
            node.signal_id = mapping[node.symbol]

    for spec_section in program.get_spec_sections():
        postorder(spec_section, assign_signal_ids_util)


def compile(
    input_filename: str,
    trace_filename: Optional[str],
    map_filename: Optional[str],
    impl: str = "c",
    custom_mission_time: int = -1,
    int_width: int = 8,
    int_signed: bool = False,
    float_width: int = 32,
    output_filename: str = "r2u2_spec.bin",
    enable_assemble: bool = True,
    enable_cse: bool = False,
    enable_at: bool = False,
    enable_bz: bool = False,
    enable_extops: bool = False,
    enable_rewrite: bool = False,
    quiet: bool = False
) -> ReturnCode:
    """Compile a C2PO input file, output generated R2U2 binaries and return error/success code.
    
    Args:
        input_filename: Name of a C2PO input file
        trace_filename:
        map_filename:
        impl: An R2U2 implementation to target. Should be one of 'c', 'c++', 'cpp', 'fpga', or 'vhdl'
        int_width: Width to set C2PO INT type to. Should be one of 8, 16, 32, or 64
        mission_time: Value of mission-time to replace "M" with in specs
        int_signed: If true sets INT type to signed
        float_width: Width to set C2PO FLOAT type to. Should be one of 32 or 64
        output_filename: Name of binary output file
        enable_assemble: If true outputs binary to output_filename
        enable_cse: If true enables Common Subexpression Elimination
        enable_at: If true enables Atomic Checker instructions
        enable_bz: If true enables Booleanizer instructions
        enable_extops: If true enables TL extended operators
        enable_rewrite: If true enables MLTL rewrite rule optimizations
        quiet: If true disables assembly output to stdout
    """
    if not set_options(impl, int_width, int_signed, float_width, 
                        enable_at, enable_bz, enable_extops):
        logger.error("Invalid configuration options.")
        return ReturnCode.INVALID_OPTIONS
    
    (input_path, trace_path, map_path) = configure_paths(input_filename, trace_filename, map_filename)

    if not input_path:
        logger.error("Cannot open input file.")
        return ReturnCode.FILE_IO_ERR

    with open(input_path, "r") as f:
        program: C2POProgram|None = parse(f.read())

    if not program:
        logger.error("Failed parsing.")
        return ReturnCode.PARSE_ERR

    # type check
    (well_typed, context) = type_check(program, str_to_r2u2_implementation(impl), enable_at, enable_bz)
    if not well_typed:
        logger.error("Failed type check.")
        return ReturnCode.TYPE_CHECK_ERR

    rewrite_definitions(program, context)
    rewrite_function_calls(program, context)
    rewrite_contracts(program, context)
    rewrite_set_aggregation(program)
    rewrite_struct_accesses(program)

    if enable_rewrite:
        optimize_rewrite_rules(program)

    # rewrite without extended operators if enabled
    if not enable_extops:
        rewrite_extended_operators(program)

    # common sub-expressions elimination
    if enable_cse:
        optimize_cse(program)

    if not enable_assemble:
        return ReturnCode.SUCCESS
    
    signal_mapping: Optional[SignalMapping] = None
    mission_time: Optional[int] = None

    if trace_path:
        (mission_time, signal_mapping) = process_trace_file(trace_path, map_path is None)
    
    if map_path:
        signal_mapping = process_map_file(map_path)

    if not signal_mapping:
        logger.error("No map file nor header provided in trace file; cannot perform signal mapping")
        return ReturnCode.ERROR
    
    assign_signal_ids(program, signal_mapping)

    # disregard inferred mission time if given explicitly
    if custom_mission_time > -1:
        mission_time = custom_mission_time
        
        # warn if the given trace is shorter than the defined mission time
        if custom_mission_time > mission_time:
            logger.warning(f"Given mission time ({custom_mission_time}) is greater than length of trace ({mission_time}).")

    # generate alias file
    aliases = generate_aliases(program, context)

    # generate assembly
    (bz_asm, at_asm, ft_asm, pt_asm) = generate_assembly(program, context)
    scq_asm: List[Tuple[int,int]] = generate_scq_assembly(program)

    # print assembly if 'quiet' option not enabled
    if not quiet:
        if enable_at:
            logger.info(Color.HEADER+"AT Assembly"+Color.ENDC+":")
            for s in at_asm:
                logger.info(f"\t{s}")
        if enable_bz:
            logger.info(Color.HEADER+"BZ Assembly"+Color.ENDC+":")
            for s in bz_asm:
                logger.info(f"\t{s}")

        logger.info(Color.HEADER+"FT Assembly"+Color.ENDC+":")
        for a in ft_asm:
            logger.info(f"\t{a}")

        logger.info(Color.HEADER+"PT Assembly"+Color.ENDC+":")
        for a in pt_asm:
            logger.info(f"\t{a}")

        logger.info(Color.HEADER+"SCQ Assembly"+Color.ENDC+":")
        for s in scq_asm:
            logger.info(f"\t{s}")

        logger.info(Color.HEADER+"Aliases"+Color.ENDC+":")
        for a in aliases:
            logger.info(f"\t{a}")

    # assemble(output_filename, at_asm, bz_asm, ft_asm, scq_asm, pt_asm, aliases)

    return ReturnCode.SUCCESS

