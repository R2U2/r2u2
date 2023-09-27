from __future__ import annotations
from typing import Dict, List, Tuple
import sys
import re

from .logger import logger, Color
from .ast import *
from .type_check import type_check
from .rewrite import *
from .parse import parse
from .assembler import assemble


class ReturnCode(Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERROR = 2
    TYPE_CHECK_ERROR = 3
    ASM_ERROR = 4
    INVALID_OPTIONS = 5

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


def parse_signals(filename: str) -> Dict[str,int]:
    """Opens filename and constructs a dictionary mapping signal names to their order in the file. If filename is a csv file, uses the header for signal mapping. Otherwise filename is treated as a map file and uses the given order for signal mapping.
    
    Args:
        filename: Name of file to be read

    Returns:
        dict mapping signal names to their oder in the csv or mapping file
    """
    mapping: Dict[str,int] = {}

    if re.match(".*\\.csv",filename):
        with open(filename,"r") as f:
            text: str = f.read()
            lines: List[str] = text.splitlines()

            if len(lines) < 1:
                logger.error(f" Not enough data in file '{filename}'")
                return {}

            cnt: int = 0

            if lines[0][0] != "#":
                logger.error(f" Header missing in signals file.")
                return {}

            header = lines[0][1:]

            for id in [s.strip() for s in header.split(",")]:
                if id in mapping:
                    logger.warning(f" Signal ID '{id}' found multiple times in csv, using right-most value.")
                mapping[id] = cnt
                cnt += 1
    else: 
        with open(filename,"r") as f:
            text: str = f.read()
            cnt: int = 0

            for line in text.splitlines():
                if re.match("[a-zA-Z_]\\w*:\\d+", line):
                    strs = line.split(":")
                    id = strs[0]
                    sid = int(strs[1])

                    if id in mapping:
                        logger.warning(f" Signal ID '{id}' found multiple times in map file, using latest value.")

                    mapping[id] = sid
                else:
                    logger.error(f" Invalid format for map line (found {line})\n\t Should be of the form SYMBOL ':' NUMERAL")
                    return {}

    return mapping


def optimize_cse(program: C2POProgram) :
    """
    Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence. Applies CSE to FT/PT formulas separately.

    Preconditions:
        - `program` is type correct.

    Postconditions:
        - Sets of FT/PT specifications have no distinct, syntactically equivalent sub-expressions (i.e., is CSE-reduced).
        - Some nodes in AST may have multiple parents.
    """
    S: Dict[str, C2PONode]

    def optimize_cse_util(node: C2PONode) :
        nonlocal S

        if str(node) in S:
            node.replace(S[str(node)])
        else:
            S[str(node)] = node

    for spec in program.get_spec_sections():
        S = {}
        postorder(spec, optimize_cse_util)

    # TODO: How to do this with potentially many SPEC sections?
    # postorder_iterative(program.get_future_time_spec_sections(), optimize_cse_util)
    # S = {k:v for (k,v) in S.items() if isinstance(v, BZInstruction)}
    # postorder_iterative(program.get_pt_specs(), optimize_cse_util)

    program.is_cse_reduced = True


def generate_aliases(program: C2POProgram) -> List[str]:
    """
    Generates strings corresponding to the alias file for the argument program. The alias file is used by R2U2 to print formula labels and contract status.

    Preconditions:
        - program is type correct

    Postconditions:
        - None
    """
    s: List[str] = []

    specs = [s.get_specs() for s in program.get_spec_sections()]

    for spec in specs:
        if spec.symbol in program.contracts:
            # then formula is part of contract, ignore
            continue
        if isinstance(spec, C2POSpecification):
            s.append(f"F {spec.symbol} {spec.formula_number}")

    for label,fnums in program.contracts.items():
        s.append(f"C {label} {fnums[0]} {fnums[1]} {fnums[2]}")

    return s


# def generate_assembly(program: C2POProgram, at: bool, bz: bool) -> Tuple[List[TLInstruction], List[TLInstruction], List[BZInstruction], List[ATInstruction]]:
#     formula_type: FormulaType
#     ftid: int = 0
#     ptid: int = 0
#     bzid: int = 0
#     atid: int = 0

#     ft_asm = []
#     pt_asm = []
#     bz_asm = []
#     at_asm = []

#     def assign_ftids(node: C2PONode) :
#         nonlocal ftid, bzid, atid

#         if isinstance(node, TLInstruction):
#             node.ftid = ftid
#             ftid += 1

#         if isinstance(node, BZInstruction):
#             if node.bzid < 0:
#                 node.bzid = bzid
#                 bzid += 1

#             if node.has_tl_parent():
#                 node.ftid = ftid
#                 ftid += 1
#                 if node.atid < 0:
#                     node.atid = atid
#                     atid += 1

#         if isinstance(node, C2POAtomic):
#             # Retrieve cached atomic number from program.atomics, assign from
#             # atid counter on first lookup
#             #
#             # Key exception possible if atomic node does not appear in atomics
#             if program.atomics[node.name].atid == -1:
#                 node.atid = atid
#                 program.atomics[node.name].atid = atid
#                 atid += 1
#             else:
#                 node.atid = program.atomics[node.name].atid

#     def assign_ptids(node: C2PONode) :
#         nonlocal ptid, bzid, atid

#         if isinstance(node, TLInstruction):
#             node.ptid = ptid
#             ptid += 1

#         if isinstance(node, BZInstruction):
#             if node.bzid < 0:
#                 node.bzid = bzid
#                 bzid += 1

#             if node.has_tl_parent():
#                 node.ptid = ptid
#                 ptid += 1
#                 if node.atid < 0:
#                     node.atid = atid
#                     atid += 1

#         if isinstance(node, C2POAtomic):
#             # Retrieve cached atomic number from program.atomics, assign from
#             # atid counter on first lookup
#             #
#             # Key exception possible if atomic node does not appear in atomics
#             if program.atomics[node.name].atid == -1:
#                 node.atid = atid
#                 program.atomics[node.name].atid = atid
#                 atid += 1
#             else:
#                 node.atid = program.atomics[node.name].atid


#     def generate_assembly_util(node: C2PONode) :
#         nonlocal formula_type

#         if isinstance(node, Instruction):
#             if formula_type == FormulaType.FT and node.ftid > -1:
#                 ft_asm.append(node)
#             elif formula_type == FormulaType.PT and node.ptid > -1:
#                 pt_asm.append(node)
#             if node.bzid > -1 and not node in bz_asm:
#                 bz_asm.append(node)
#         elif not isinstance(node, C2POBool):
#             logger.critical(f" Invalid node type for assembly generation (found '{type(node)}').")

#     postorder_iterative(program.get_ft_specs(), assign_ftids)
#     postorder_iterative(program.get_pt_specs(), assign_ptids)

#     formula_type = FormulaType.FT
#     postorder_iterative(program.get_ft_specs(), generate_assembly_util)
#     formula_type = FormulaType.PT
#     postorder_iterative(program.get_pt_specs(), generate_assembly_util)

#     for at_instr in [a for a in program.atomics.values() if a.atid >= 0]:
#         at_asm.append(at_instr)

#     at_asm.sort(key=lambda n: n.atid)
#     bz_asm.sort(key=lambda n: n.bzid)
#     ft_asm.sort(key=lambda n: n.ftid)
#     pt_asm.sort(key=lambda n: n.ptid)

#     return (ft_asm, pt_asm, bz_asm, at_asm)


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


def compile(
    input_filename: str,
    trace_filename: Optional[str],
    map_filename: Optional[str],
    impl: str = "c",
    mission_time: int = -1,
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
) -> int:
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
        logger.error(" Invalid configuration options.")
        return ReturnCode.INVALID_OPTIONS.value

    with open(input_filename, "r") as f:
        program: C2POProgram|None = parse(f.read())

    if not program:
        logger.error(" Failed parsing.")
        return ReturnCode.PARSE_ERROR.value

    # type check
    (well_typed, context) = type_check(program, str_to_r2u2_implementation(impl), enable_at, enable_bz)
    if not well_typed:
        logger.error(" Failed type check.")
        return ReturnCode.TYPE_CHECK_ERROR.value

    rewrite_defs_and_structs(program, context)
    rewrite_contracts(program)
    rewrite_set_aggregation(program)
    print(program)
    sys.exit()
    rewrite_struct_access(program)
    

    # if enable_rewrite:
    #     optimize_rewrite_rules(program)

    # # rewrite without extended operators if enabled
    # if not enable_extops:
    #     rewrite_extended_operators(program)

    # # common sub-expressions elimination
    # if enable_cse:
    #     optimize_cse(program)

    sys.exit()

    # parse csv/signals file
    program.signal_mapping = parse_signals(signals_filename)

    # generate alias file
    aliases = generate_aliases(program)

    # generate assembly
    (ft_asm, pt_asm, bz_asm, at_asm) = generate_assembly(program, enable_at, enable_bz)
    scq_asm: List[Tuple[int,int]] = generate_scq_assembly(program)

    # print assembly if 'quiet' option not enabled
    if not quiet:
        if enable_at:
            logger.info(Color.HEADER+"AT Assembly"+Color.ENDC+":")
            for s in at_asm:
                logger.info(f"\t{s.at_asm()}")
        if enable_bz:
            logger.info(Color.HEADER+"BZ Assembly"+Color.ENDC+":")
            for s in bz_asm:
                logger.info(f"\t{s.bz_asm()}")

        logger.info(Color.HEADER+"FT Assembly"+Color.ENDC+":")
        for a in ft_asm:
            logger.info(f"\t{a.ft_asm()}")

        logger.info(Color.HEADER+"PT Assembly"+Color.ENDC+":")
        for a in pt_asm:
            logger.info(f"\t{a.pt_asm()}")

        logger.info(Color.HEADER+"SCQ Assembly"+Color.ENDC+":")
        for s in scq_asm:
            logger.info(f"\t{s}")

        logger.info(Color.HEADER+"Aliases"+Color.ENDC+":")
        for a in aliases:
            logger.info(f"\t{a}")

    if enable_assemble:
        assemble(output_filename, at_asm, bz_asm, ft_asm, scq_asm, pt_asm, aliases)

    return (ReturnCode.SUCCESS.value, ft_asm, pt_asm, bz_asm, at_asm, scq_asm)

