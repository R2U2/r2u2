# C2PO Commands Reference

_Auto-generated on 2026-04-15 by `compiler/scripts/generate_commands_doc.py`._

Total commands: **58**

## Source: `assemble.py`

### `unsafe_assemble`

Assemble a program into a binary. Does not compute atomics or SCQ sizes beforehand. Use at your own risk, will fail if atomics or SCQ sizes are not computed or were computed before the program was modified.

```text
usage: unsafe_assemble [-h] [--assembly-filename ASSEMBLY_FILENAME]
                       [--print | --no-print] [--aux | --no-aux]
                       binary-filename
```

#### Options

- `binary-filename` (required, type: `str`, default: none) - The filename to write the binary to
- `assembly-filename` (optional, type: `str`, default: none) - The filename to write the assembly to
- `print` (optional, type: `bool`, default: `False`) - Print the assembly to the console
- `aux` (optional, type: `bool`, default: `True`) - Enable aux data (e.g., contract status and specification naming)

### `write_bounds_c`

Write bounds file for C

```text
usage: write_bounds_c [-h] [--print | --no-print] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The filename to write the bounds file to
- `print` (optional, type: `bool`, default: `False`) - Print the bounds file to the console

### `write_bounds_rust`

Write bounds file for rust

```text
usage: write_bounds_rust [-h] [--print | --no-print] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The filename to write the bounds file to
- `print` (optional, type: `bool`, default: `False`) - Print the bounds file to the console

## Source: `atomics.py`

### `compute_atomics`

Compute atomics and store them in the context. Likely does not need to be run manually. An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine. Syntactically equivalent expressions share the same atomic ID.

```text
usage: compute_atomics [-h]
```

No options.

## Source: `command.py`

### `assemble`

Assemble a program into a binary. Computes atomics and SCQ sizes beforehand.

```text
usage: assemble [-h] [--scq-constant SCQ_CONSTANT]
                [--assembly-filename ASSEMBLY_FILENAME] [--print | --no-print]
                [--aux | --no-aux]
                binary-filename
```

#### Commands included in this composite command

- `compute_atomics`
- `compute_scq_sizes`
- `unsafe_assemble`

#### Options

- `scq-constant` (optional, type: `int`, default: `0`) - A constant to add to the SCQ size of each node
- `binary-filename` (required, type: `str`, default: none) - The filename to write the binary to
- `assembly-filename` (optional, type: `str`, default: none) - The filename to write the assembly to
- `print` (optional, type: `bool`, default: `False`) - Print the assembly to the console
- `aux` (optional, type: `bool`, default: `True`) - Enable aux data (e.g., contract status and specification naming)

### `compile`

Compile a program after parsing with basic optimizations. No dependencies on external tools.

```text
usage: compile [-h] [--scq-constant SCQ_CONSTANT]
               [--assembly-filename ASSEMBLY_FILENAME] [--print | --no-print]
               [--aux | --no-aux]
               binary-filename
```

#### Commands included in this composite command

- `type_check`
- `desugar`
- `optimize_rewrites`
- `remove_extended_operators`
- `multi_operators_to_binary`
- `optimize_cse`
- `assemble`

#### Options

- `scq-constant` (optional, type: `int`, default: `0`) - A constant to add to the SCQ size of each node
- `binary-filename` (required, type: `str`, default: none) - The filename to write the binary to
- `assembly-filename` (optional, type: `str`, default: none) - The filename to write the assembly to
- `print` (optional, type: `bool`, default: `False`) - Print the assembly to the console
- `aux` (optional, type: `bool`, default: `True`) - Enable aux data (e.g., contract status and specification naming)

### `desugar`

A list of commands to desugar a program. Only C2PO programs need to be desugared.

```text
usage: desugar [-h]
```

#### Commands included in this composite command

- `expand_definitions`
- `convert_function_calls_to_structs`
- `resolve_contracts`
- `resolve_enum_references`
- `resolve_struct_accesses`
- `resolve_array_accesses`
- `unroll_set_aggregation`
- `resolve_struct_accesses`
- `unroll_array_accesses`
- `resolve_struct_accesses`

No options.

### `disable_booleanizer`

Disable Booleanizer expressions

```text
usage: disable_booleanizer [-h]
```

No options.

### `enable_booleanizer`

Enable Booleanizer expressions

```text
usage: enable_booleanizer [-h]
```

No options.

### `help`

Print the help message

```text
usage: help [-h]
```

No options.

### `print_c2po`

Print the C2PO representation of the program

```text
usage: print_c2po [-h]
```

No options.

### `print_mltl`

Print the MLTL representation of the program

```text
usage: print_mltl [-h]
```

No options.

### `print_prefix`

Print the prefix representation each specification in the program

```text
usage: print_prefix [-h]
```

No options.

### `print_stats`

Print the statistics according to the given format string

```text
usage: print_stats [-h] format
```

#### Options

- `format` (required, type: `str`, default: none) - The format string to use for the statistics. Run `print_stats_format` to see the valid placeholders and escape sequences.

### `print_stats_format`

Print the possible placeholders and escape sequences in the format string for the statistics

```text
usage: print_stats_format [-h]
```

No options.

### `set_debug`

Set debug (set log level to maximum value)

```text
usage: set_debug [-h]
```

No options.

### `set_egglog_path`

Set the path to the egglog executable

```text
usage: set_egglog_path [-h] egglog-path
```

#### Options

- `egglog-path` (required, type: `str`, default: none) - Path to egglog executable

### `set_log_level`

Set the log level

```text
usage: set_log_level [-h] log_level
```

#### Options

- `log_level` (required, type: `int`, default: `0`) - The log level

### `set_mission_time`

Set the mission time

```text
usage: set_mission_time [-h] mission-time
```

#### Options

- `mission-time` (required, type: `int`, default: none) - Set the mission time (M variable)

### `set_r2u2_bin_path`

Set the path to the R2U2 binary

```text
usage: set_r2u2_bin_path [-h] r2u2-bin-path
```

#### Options

- `r2u2-bin-path` (required, type: `str`, default: none) - Path to R2U2 binary

### `set_r2u2_c_path`

Set the directory containing the R2U2 C code

```text
usage: set_r2u2_c_path [-h] r2u2-c-path
```

#### Options

- `r2u2-c-path` (required, type: `str`, default: `/home/cgjohann/Git/r2u2/compiler/c2po/../../monitors/c`) - Directory containing the R2U2 C code

### `set_smt_solver_path`

Set the path to the SMT solver executable

```text
usage: set_smt_solver_path [-h] smt-solver-path
```

#### Options

- `smt-solver-path` (required, type: `str`, default: none) - Path to SMT solver executable

## Source: `cse.py`

### `optimize_cse`

Performs syntactic common sub-expression elimination on program. Applies CSE to FT/PT formulas separately.

```text
usage: optimize_cse [-h]
```

No options.

## Source: `desugar.py`

### `convert_function_calls_to_structs`

Converts each function call in `program` that corresponds to a struct instantiation to a `cpt.Struct`.

```text
usage: convert_function_calls_to_structs [-h]
```

No options.

### `expand_definitions`

Expands each definition symbol in the definitions and specifications of `program` to its expanded definition. This is essentially macro expansion.

```text
usage: expand_definitions [-h]
```

No options.

### `resolve_array_accesses`

Resolves array access operations to the underlying member expression.

```text
usage: resolve_array_accesses [-h]
```

No options.

### `resolve_contracts`

Removes each contract from each specification in Program and adds the corresponding conditions to track.

```text
usage: resolve_contracts [-h]
```

No options.

### `resolve_enum_references`

Resolves each enum member to its underlying value.

```text
usage: resolve_enum_references [-h]
```

No options.

### `resolve_struct_accesses`

Resolves struct access operations to the underlying member expression.

```text
usage: resolve_struct_accesses [-h]
```

No options.

### `unroll_array_accesses`

Unrolls array operators into equivalent engine-supported operations e.g., array1 == array2 is rewritten into a conjunction.

```text
usage: unroll_array_accesses [-h]
```

No options.

### `unroll_set_aggregation`

Unrolls set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction.

```text
usage: unroll_set_aggregation [-h]
```

No options.

## Source: `eqsat.py`

### `optimize_eqsat`

Optimize the program via EQSat

```text
usage: optimize_eqsat [-h] [--rewrites {incomplete,complete}]
                      [--extraction-method {heuristic,optimal}]
                      [--associative | --no-associative]
                      [--commutative | --no-commutative]
                      [--multi-arity | --no-multi-arity]
                      [--const-folding | --no-const-folding]
                      [--extended | --no-extended]
                      [--temporal | --no-temporal]
                      [--egglog-max-time EGGLOG_MAX_TIME]
                      [--egglog-max-memory EGGLOG_MAX_MEMORY]
                      [--egglog-bin EGGLOG_BIN]
                      [--gurobi-max-time GUROBI_MAX_TIME]
                      [--gurobi-max-memory GUROBI_MAX_MEMORY]
                      [--check-equiv | --no-check-equiv]
                      [--equiv-smt-encoding-filename EQUIV_SMT_ENCODING_FILENAME]
                      [--theory {uflia,qf_uflia,qf_bv}]
                      [--smt-max-time SMT_MAX_TIME]
                      [--smt-max-memory SMT_MAX_MEMORY]
```

#### Options

- `rewrites` (optional, type: `str`, default: `incomplete`, choices: `incomplete, complete`) - The set of rewrites to enable
- `extraction-method` (optional, type: `str`, default: `heuristic`, choices: `heuristic, optimal`) - The method to use for extraction
- `associative` (optional, type: `bool`, default: `True`) - Whether to enable associative rewrites
- `commutative` (optional, type: `bool`, default: `True`) - Whether to enable commutative rewrites
- `multi-arity` (optional, type: `bool`, default: `True`) - Whether to enable multi-arity rewrites
- `const-folding` (optional, type: `bool`, default: `True`) - Whether to enable const folding
- `extended` (optional, type: `bool`, default: `True`) - Whether to enable extended operator rewrites
- `temporal` (optional, type: `bool`, default: `True`) - Whether to enable temporal rewrites
- `egglog-max-time` (optional, type: `int`, default: `5`) - The maximum time to allow for egglog in seconds
- `egglog-max-memory` (optional, type: `int`, default: `0`) - The maximum memory to allow for egglog in MB, use 0 for no maximum
- `egglog-bin` (optional, type: `str`, default: none) - The path to the egglog executable
- `gurobi-max-time` (optional, type: `int`, default: `10`) - The maximum time to allow for Gurobi in seconds if `extraction-method` is `optimal`
- `gurobi-max-memory` (optional, type: `int`, default: `0`) - The maximum memory to allow for Gurobi in MB, use 0 for no maximum if `extraction-method` is `optimal`
- `check-equiv` (optional, type: `bool`, default: `False`) - Whether to check equivalence of the optimized formula
- `equiv-smt-encoding-filename` (optional, type: `str`, default: none) - The path to write the SMT encoding for equivalence checking to
- `theory` (optional, type: `str`, default: `uflia`, choices: `uflia, qf_uflia, qf_bv`) - The SMT theory to use if `check-equiv` is enabled
- `smt-max-time` (optional, type: `int`, default: `5`) - The maximum time to allow for the SMT solver in seconds
- `smt-max-memory` (optional, type: `int`, default: `0`) - The maximum memory to allow for the SMT solver in MB, use 0 for no maximum

### `write_eqsat_encoding`

Write the EQSat encoding for the program

```text
usage: write_eqsat_encoding [-h] [--formula FORMULA]
                            [--heuristic-extraction | --no-heuristic-extraction]
                            [--rewrites {incomplete,complete}]
                            [--associative | --no-associative]
                            [--commutative | --no-commutative]
                            [--multi-arity | --no-multi-arity]
                            [--const-folding | --no-const-folding]
                            [--temporal | --no-temporal]
                            location
```

#### Options

- `location` (required, type: `str`, default: none) - The path to write the EQSat encoding to
- `formula` (optional, type: `str`, default: none) - The formula to write the EQSat encoding for. If not provided, all formulas will be written
- `heuristic-extraction` (optional, type: `bool`, default: `False`) - Whether to enable heuristic extraction of the egglog output
- `rewrites` (optional, type: `str`, default: `incomplete`, choices: `incomplete, complete`) - The set of rewrites to enable
- `associative` (optional, type: `bool`, default: `True`) - Whether to enable associative rewrites
- `commutative` (optional, type: `bool`, default: `True`) - Whether to enable commutative rewrites
- `multi-arity` (optional, type: `bool`, default: `True`) - Whether to enable multi-arity rewrites
- `const-folding` (optional, type: `bool`, default: `True`) - Whether to enable const folding rewrites
- `temporal` (optional, type: `bool`, default: `True`) - Whether to enable temporal and logical rewrites

## Source: `map.py`

### `generate_map`

Generate a signal mapping for a given program. If the program already has a valid signal mapping, this will only output the mapping to the map file. The map file will assign indices based on the order the signals are declared in the program. 

```text
usage: generate_map [-h] [--output OUTPUT]
```

#### Options

- `output` (optional, type: `str`, default: none) - The path to the output map file

### `parse_map`

Parse a map file and add the signal mapping to the context

```text
usage: parse_map [-h] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The path to the map file

## Source: `parse_c2po.py`

### `parse_c2po`

Parse a C2PO input file and return a program

```text
usage: parse_c2po [-h] [--mission-time MISSION_TIME] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The path to the C2PO input file
- `mission-time` (optional, type: `int`, default: `-1`) - The mission time

## Source: `parse_equiv.py`

### `parse_equiv`

Parse a MLTL equivalence specification and return a program

```text
usage: parse_equiv [-h] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The path to the MLTL equivalence specification file

## Source: `parse_mltl.py`

### `parse_mltl`

Parse an MLTL input file and return a program

```text
usage: parse_mltl [-h] [--mission-time MISSION_TIME] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The path to the MLTL input file
- `mission-time` (optional, type: `int`, default: `-1`) - The mission time

## Source: `r2u2.py`

### `run_r2u2`

Run R2U2 over the trace attached to the context using the assembly attached to the context.

```text
usage: run_r2u2 [-h] [--num-runs NUM_RUNS] [--print | --no-print]
                [--output OUTPUT] [--r2u2dir R2U2DIR]
                binary trace
```

#### Options

- `binary` (required, type: `str`, default: none) - The filename for the spec binary.
- `trace` (required, type: `str`, default: none) - The filename of the trace to run over.
- `num-runs` (optional, type: `int`, default: `1`) - The number of times to run R2U2.
- `print` (optional, type: `bool`, default: `False`) - Print the R2U2 output to the console.
- `output` (optional, type: `str`, default: none) - The filename to write the R2U2 output to.
- `r2u2dir` (optional, type: `str`, default: none) - The directory to run R2U2 in.

## Source: `rewrite.py`

### `optimize_rewrites`

Applies MLTL rewrite rules in a single pass of the expression tree to reduce required SCQ memory.

```text
usage: optimize_rewrites [-h]
```

No options.

## Source: `sat.py`

### `check_equiv`

Check that all formulas in the program are equivalent using the SMT encoding

```text
usage: check_equiv [-h] [--strict | --no-strict] [--quiet | --no-quiet]
                   [--smt-max-time SMT_MAX_TIME]
                   [--smt-max-memory SMT_MAX_MEMORY]
                   {uflia,qf_uflia,qf_bv}
```

#### Options

- `theory` (required, type: `str`, default: none, choices: `uflia, qf_uflia, qf_bv`) - The SMT theory to use
- `strict` (optional, type: `bool`, default: `False`) - Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.
- `quiet` (optional, type: `bool`, default: `False`) - Whether to print the results of the equivalence checks.
- `smt-max-time` (optional, type: `int`, default: `5`) - The maximum time to allow for the SMT solver in seconds
- `smt-max-memory` (optional, type: `int`, default: `0`) - The maximum memory to allow for the SMT solver in MB, use 0 for no maximum

### `check_sat`

Check the satisfiability of the program using the SMT encoding

```text
usage: check_sat [-h] [--strict | --no-strict] [--print | --no-print]
                 [--smt-max-time SMT_MAX_TIME]
                 [--smt-max-memory SMT_MAX_MEMORY]
                 {uflia,qf_uflia,qf_bv}
```

#### Options

- `theory` (required, type: `str`, default: none, choices: `uflia, qf_uflia, qf_bv`) - The SMT theory to use
- `strict` (optional, type: `bool`, default: `False`) - Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.
- `print` (optional, type: `bool`, default: `False`) - Whether to print the results of the satisfiability checks. If not provided, unsat and unknown results will be sent as warnings.
- `smt-max-time` (optional, type: `int`, default: `5`) - The maximum time to allow for the SMT solver in seconds
- `smt-max-memory` (optional, type: `int`, default: `0`) - The maximum memory to allow for the SMT solver in MB, use 0 for no maximum

### `write_equiv_smt_encoding`

Write the SMT encoding(s) for the equivalence of all formulas in the program to the given location. If there are more than two formulas, the encodings will be written to a directory.

```text
usage: write_equiv_smt_encoding [-h] [--strict | --no-strict]
                                location {uflia,qf_uflia,qf_bv}
```

#### Options

- `location` (required, type: `str`, default: none) - The path to write the SMT encoding(s) to
- `theory` (required, type: `str`, default: none, choices: `uflia, qf_uflia, qf_bv`) - The SMT theory to use
- `strict` (optional, type: `bool`, default: `False`) - Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.

### `write_smt_encoding`

Write the SMT encoding for the program or formula to the given location

```text
usage: write_smt_encoding [-h] [--strict | --no-strict] [--formula FORMULA]
                          location {uflia,qf_uflia,qf_bv}
```

#### Options

- `location` (required, type: `str`, default: none) - The path to write the SMT encoding to
- `theory` (required, type: `str`, default: none, choices: `uflia, qf_uflia, qf_bv`) - The SMT theory to use
- `strict` (optional, type: `bool`, default: `False`) - Whether to use the strict SMT encoding. If not provided, the encoding will be non-strict. Strict encoding checks whether a trace of any length satisfies the encoding, non-strict encoding only checks whether a trace of length cplen satisfies the encoding.
- `formula` (optional, type: `str`, default: none) - The formula to write the SMT encoding for. If not provided, all formulas will be written

## Source: `scq.py`

### `compute_scq_sizes`

Compute SCQ sizes for the program. Likely does not need to be run manually.

```text
usage: compute_scq_sizes [-h] [--scq-constant SCQ_CONSTANT]
```

#### Options

- `scq-constant` (optional, type: `int`, default: `0`) - A constant to add to the SCQ size of each node

## Source: `serialize.py`

### `write_c2po`

Write the C2PO representation of the program to the given filename.

```text
usage: write_c2po [-h] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The filename to write the C2PO representation to

### `write_mltl`

Write the MLTL standard representation of the program to the given filename.

```text
usage: write_mltl [-h] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The filename to write the MLTL standard representation to

### `write_pickle`

Write the pickle representation of the program to the given filename.

```text
usage: write_pickle [-h] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The filename to write the pickle representation to

### `write_prefix`

Write the prefix representation of the program to the given filename.

```text
usage: write_prefix [-h] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The filename to write the prefix representation to

## Source: `trace.py`

### `generate_trace`

Generate a random trace for a given program.

```text
usage: generate_trace [-h] [--seed SEED] [--float-precision FLOAT_PRECISION]
                      [--output OUTPUT] [--print | --no-print]
                      length min max
```

#### Options

- `length` (required, type: `int`, default: `10`) - The length of the trace
- `min` (required, type: `float`, default: `0.0`) - The minimum value for numeric types
- `max` (required, type: `float`, default: `100.0`) - The maximum value for numeric types
- `seed` (optional, type: `int`, default: none) - The seed for the random number generator
- `float-precision` (optional, type: `int`, default: `5`) - The number of decimal places for floating point numbers
- `output` (optional, type: `str`, default: none) - The path to the output trace file
- `print` (optional, type: `bool`, default: `False`) - Whether to print the trace to the console

### `parse_trace`

Parse a trace file and add the signal mapping and trace length to the context

```text
usage: parse_trace [-h] filename
```

#### Options

- `filename` (required, type: `str`, default: none) - The path to the trace file

## Source: `transform.py`

### `flatten_multi_operators`

Flatten all multi-arity operators (i.e., &&, ||, +, *)

```text
usage: flatten_multi_operators [-h]
```

No options.

### `multi_operators_to_binary`

Convert all multi-arity operators (e.g., &&, ||, +) to binary

```text
usage: multi_operators_to_binary [-h]
```

No options.

### `remove_extended_operators`

Remove extended operators (xor, ->, F, G, O, H) from the program and make all operators binary

```text
usage: remove_extended_operators [-h]
```

No options.

### `sort_operands_by_pd`

Sort all operands of commutative operators by increasing worst-case propagation delay

```text
usage: sort_operands_by_pd [-h]
```

No options.

### `to_bnf`

Convert program formulas to Boolean Normal Form (BNF)

```text
usage: to_bnf [-h]
```

No options.

### `to_nnf`

Convert program formulas to Negative Normal Form (NNF)

```text
usage: to_nnf [-h]
```

No options.

## Source: `type_check.py`

### `type_check`

Type check the program and construct a context.

```text
usage: type_check [-h]
```

No options.
