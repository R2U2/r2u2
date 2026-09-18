# C2PO

C2PO (Configuration Compiler for Property Organization) is the formula compiler for R2U2.
Documentation can be found [here](https://r2u2.github.io/r2u2/_collections/c2po_docs/user/toc.html).

## Requirements

C2PO requires Python 3.9 or newer.

To enable equality saturation, install [Rust](https://www.rust-lang.org/tools/install), then run
`scripts/setup_egglog.sh`.

To enable satisfiability checking, install [Z3](https://github.com/Z3Prover/z3). On debian-based
systems, this can be done via `sudo apt-get install z3`. You can use any SMTLIB2-compatible solver by
setting the executable path via the `--smt-solver` option. For example, using
[Yices2](https://yices.csl.sri.com/) instead, you can set `--smt-solver path/to/yices-smt2`.

## Usage

C2PO is invoked through `c2po.py` in one of three modes: CLI, script, or interactive.

### CLI Mode

To compile a specification, pass it with `--spec`. C2PO files also need a signal mapping via
`--trace` or `--map`. For example, to compile the CAV example with the Booleanizer frontend using a
simulated trace file to map input signals:

    python3 c2po.py --booleanizer --trace ../examples/cav.csv --spec ../examples/cav.c2po

A simpler compile using an explicit map file:

    python3 c2po.py --spec ../examples/simple.c2po --map ../examples/simple.map --output spec.bin

The assembled binary is written to `spec.bin` by default (`-o` / `--output`) and is ready to be run
by a properly configured R2U2 over input data.

For full compiler options:

    python3 c2po.py -h

### Script Mode

To run a file of C2PO commands (one command per line):

    python3 c2po.py --script ../examples/simple.cmd

Relative paths in a script are resolved from the script file's directory. See `docs/user/repl.md`
and `docs/user/commands.md` for command syntax.

### Interactive Mode

To start the REPL:

    python3 c2po.py --interactive

The prompt is `c2po>`. Type `help` for available commands, or `exit` to quit.

## Input Files

C2PO supports input files written in its custom input language and in the MLTL standard format.
C2PO input files must have the `.c2po` file extension and MLTL files must have the `.mltl`
extension. Pass either as `--spec`. See the `../examples/` and `test/` directories for sample files
in both formats.

Equivalence-checking files (`.equiv`) are used from script or interactive mode via `parse_equiv`.
See `docs/user/equiv.md`.

## Signal Mapping

To generate an R2U2-readable binary, C2PO must be given a mapping from variable names to indices in
the signal vector given to R2U2 during runtime. If given an MLTL file as input, the signals are
mapped to whatever number is in the variable symbol. If given a C2PO file as input, provide one of
the following via `--map` or `--trace`:

### Map File

A signal map file has a `.map` file extension and directly associates an index with a variable
symbol. Each line of the input file should be of the form `SYMBOL ':' NUMERAL` such that if `SYMBOL`
corresponds to a signal identifier in the C2PO file, its signal index is set to the integer value of
`NUMERAL`. Note that if `SYMBOL` is not present in the C2PO file, the line is ignored.

See `test/default.map` and `../examples/simple.map` for examples.

### CSV File

A CSV trace file given to C2PO as input has a `.csv` file extension and may represent simulated data
to run R2U2 offline. The file requires a header denoted with a '#' character as the first character
of the line.

See `../examples/cav.csv` for an example.

## Advanced Features

These features are optional. Satisfiability and equivalence checking need an SMTLIB2 solver
(typically Z3); equality saturation needs egglog. See [Requirements](#requirements).

### Satisfiability Checking

C2PO can encode future-time formulas as SMT and check whether each formula (and, if there is more
than one, their conjunction) is satisfiable. Results are `sat`, `unsat`, or `unknown`.

From the CLI, enable checking with `--check-sat`. `--compile` stops before assembly if you only want
the SAT result:

    python3 c2po.py --spec test/sat/sat_5.mltl --check-sat --compile

Useful CLI options:

- `--smt-encoding {uflia,qf_uflia,qf_bv}` - SMT theory (default: `uflia`)
- `--smt-max-time` / `--smt-max-memory` - solver resource limits
- `--smt-solver` - path to an SMTLIB2-compliant executable (otherwise C2PO searches `PATH`)

In script or interactive mode, use `check_sat` after parsing and type checking:

    parse_mltl test/sat/sat_5.mltl
    type_check
    check_sat uflia --print

`--print` prints one line per specification. `--strict` asks whether a trace of *any* length
satisfies the formula; the default non-strict encoding only considers traces of length equal to the
computed propagation delay. `write_smt_encoding` dumps the SMT-LIB2 encoding without running a
solver.

See `test/sat/` for more examples.

### Equality Saturation

By default, C2PO applies a single-pass set of MLTL rewrite rules (`--rewrite`, on by default).
Equality saturation searches the rewrite space more systematically and extracts a minimally sized
monitor encoding with respect to SCQ size. For more information, see our paper
[here](https://doi.org/10.34727/2026/isbn.978-3-85448-093-8_28). It is disabled by default and
requires egglog.

    python3 c2po.py --spec ../examples/simple.c2po --map ../examples/simple.map --eqsat

`--eqsat` replaces the single-pass rewrite pass. Add `--eqsat-check-equiv` to SMT-check that each
extracted formula is equivalent to the original. Other common options:

- `--eqsat-max-time` / `--eqsat-max-memory` - egglog resource limits
- `--egglog-path` - explicit path to the egglog binary
- `--eqsat-const-folding`, `--eqsat-associative`, `--eqsat-commutative`, `--eqsat-multi-arity`,
  `--eqsat-temporal` - enable or disable rewrite families (`--no-...` to disable)

In script or interactive mode:

    parse_mltl test/eqsat/future_01.mltl
    type_check
    compute_atomics
    optimize_eqsat --check-equiv

`optimize_eqsat --extraction-method ilp` uses Gurobi ILP extraction instead of the default greedy
extractor. Equality saturation currently runs on each formula individually. See
`docs/user/optimizations.md` and `test/eqsat/` for details and examples.

### Equivalence Checking and Rewrite Correctness

`check_equiv` uses SMT to decide whether adjacent formulas in a program are equivalent. This is
primarily used with `.equiv` files in script or interactive mode. `check_equiv` checks pairs in
order `(f0,f1)`, `(f1,f2)`, ... and prints one of `equiv`, `not-equiv`, or `unknown`.

A `.equiv` file has optional constraint lines starting with `c:` followed by one MLTL formula per
line. Atomic signals are `a0`, `a1`, ... and interval bounds may be symbolic (`b0`, `b1`, ...):

    c: b0 >= 0
    c: b1 >= b0
    G[0,b0] a0
    !F[0,b0] !a0

Then:

    parse_equiv demo.equiv
    desugar
    check_equiv uflia --smt-max-time 5 --smt-max-memory 0

`write_equiv_smt_encoding` writes the SMT encodings used for those pairwise checks. See
`docs/user/equiv.md` and `test/equiv/`.

The same encoding is used to prove rewrite-rule correctness. Rewrite schemas live in
`scripts/rewrites/rewrites.json`. From `scripts/rewrites/`:

    python3 generate_equiv_files.py rewrites.json equiv/
    python3 generate_egglog.py equiv rewrites.json ../../c2po/egglog
    ./generate_smt2_equiv.sh equiv/ smt2/ ../../c2po.py

Each generated `.smt2` file encodes the *negation* of a rewrite's equivalence, so `unsat` means the
rewrite is valid. Dispatch the proofs with `scripts/prove.sh` (expects `z3` and `cvc5` in `PATH`):

    ../prove.sh smt2/

See `scripts/rewrites/README.md` for the full workflow.

## Testing

To run C2PO's test suite, see `test/README.md`.

## Stats Format String

In script or interactive mode, C2PO can print stats via the `print_stats` command. The format string
uses placeholders of the form `%NAME`. Run `print_stats_format` for the full list. Common
specifiers include:

- `%F` = Input filename
- `%scq` = Total SCQ size
- `%satres` = SMT solver result
- `%satenc` = SMT encoding time
- `%sattime` = SMT solver time
- `%satnc` = SMT solver number of calls
- `%eqsatenc` = Eqsat encoding time
- `%eqsattime` = Eqsat solver time
- `%eqsateqres` = Eqsat equivalence result

For example, to report some statistics from a satisfiability check, put the following in a script
and run it with `python3 c2po.py --script`:

    parse_mltl test/sat/sat_5.mltl
    type_check
    check_sat uflia --print
    print_stats "%satres,%satenc,%sattime"

