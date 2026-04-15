# CLI Options

The following options are generated from `python3 c2po.py --help`:

```text
usage: c2po.py [-h] [--version] [-s SCRIPT] [-i] [--spec SPEC] [--trace TRACE]
               [--map MAP] [-o OUTPUT] [--write-bounds WRITE_BOUNDS] [-q] [-v]
               [--debug] [-p] [-tc] [-c] [--mission-time MISSION_TIME]
               [--scq-constant SCQ_CONSTANT] [-bz] [--aux | --no-aux]
               [--cse | --no-cse] [--rewrite | --no-rewrite]
               [--extops | --no-extops] [--eqsat | --no-eqsat]
               [--eqsat-check-equiv | --no-eqsat-check-equiv]
               [--eqsat-const-folding | --no-eqsat-const-folding]
               [--eqsat-associative | --no-eqsat-associative]
               [--eqsat-commutative | --no-eqsat-commutative]
               [--eqsat-multi-arity | --no-eqsat-multi-arity]
               [--eqsat-temporal | --no-eqsat-temporal]
               [--eqsat-max-time EQSAT_MAX_TIME]
               [--eqsat-max-memory EQSAT_MAX_MEMORY]
               [--egglog-path EGGLOG_PATH] [--check-sat | --no-check-sat]
               [--smt-encoding {uflia,qf_uflia,qf_bv}]
               [--smt-max-time SMT_MAX_TIME] [--smt-max-memory SMT_MAX_MEMORY]
               [--smt-solver SMT_SOLVER]

C2PO - Configuration Compiler for Property Organization
```

## Positional Arguments

None.

## Optional Arguments

- `-h, --help` - show this help message and exit
- `--version` - print version and exit
- `-s SCRIPT, --script SCRIPT` - script file to execute, ignores all other arguments
- `-i, --interactive` - run in interactive mode, ignores all other arguments
- `--spec SPEC` - specification file (either .c2po, .mltl, or .equiv)
- `--trace TRACE` - csv file where variable names are mapped to signal order using file header
- `--map MAP` - map file where variable names are mapped to signal order
- `-o OUTPUT, --output OUTPUT` - location where specification binary will be written (default: spec.bin)
- `--write-bounds WRITE_BOUNDS` - location where bounds file will be written, must have .h or .toml extension (default: none)
- `-q, --quiet` - disable output
- `-v, --verbose` - logging verbosity, pass twice for trace logging
- `--debug` - set debug mode, implies trace logging
- `-p, --parse` - run only the parser
- `-tc, --type-check` - run only the parser and type checker
- `-c, --compile` - run only the parser, type checker, and passes
- `--mission-time MISSION_TIME` - mission time, overriding inference from a trace file if present
- `--scq-constant SCQ_CONSTANT` - increase the SCQ sizes of all nodes by this constant
- `-bz, --booleanizer` - enable booleanizer
- `--aux, --no-aux` - enable aux data (e.g., contract status and specification naming)
- `--cse, --no-cse` - enable CSE optimization
- `--rewrite, --no-rewrite` - enable MLTL rewrite rule optimizations
- `--extops, --no-extops` - enable extended operations
- `--eqsat, --no-eqsat` - enable equality saturation
- `--eqsat-check-equiv, --no-eqsat-check-equiv` - enable equivalence checking of equality saturation results
- `--eqsat-const-folding, --no-eqsat-const-folding` - enable const folding rewrite rule for equality saturation
- `--eqsat-associative, --no-eqsat-associative` - enable associative rewrite rule for equality saturation
- `--eqsat-commutative, --no-eqsat-commutative` - enable commutative rewrite rule for equality saturation
- `--eqsat-multi-arity, --no-eqsat-multi-arity` - enable multi-arity rewrite rule for equality saturation
- `--eqsat-temporal, --no-eqsat-temporal` - enable temporal rewrite rule for equality saturation
- `--eqsat-max-time EQSAT_MAX_TIME` - set the maximum time to allow for egglog in seconds (default: 5)
- `--eqsat-max-memory EQSAT_MAX_MEMORY` - set the maximum memory to allow for egglog in MB, use 0 for no maximum (default: 0)
- `--egglog-path EGGLOG_PATH` - path to egglog executable, if not set will search PATH
- `--check-sat, --no-check-sat` - enable satisfiability checking of future-time formulas
- `--smt-encoding {uflia,qf_uflia,qf_bv}` - specify the SMT encoding to use for satisfiability checking (default: uflia)
- `--smt-max-time SMT_MAX_TIME` - set the total maximum time to allow for SMT calls in seconds (default: 5)
- `--smt-max-memory SMT_MAX_MEMORY` - set the total maximum memory to allow for SMT calls in MB, use 0 for no maximum (default: 0)
- `--smt-solver SMT_SOLVER` - path to SMTLIB2-compliant executable, if not set will search for one in PATH
