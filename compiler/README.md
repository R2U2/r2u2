# C2PO

C2PO (Configuration Compiler for Property Organization) is the formula compiler for R2U2.

## Requirements

C2PO requires Python 3.8 or newer.

To enable equality saturation, install [Rust](https://www.rust-lang.org/tools/install), then run the
`setup_egglog.sh` script.

To enable satisfiability checking, install [Z3](https://github.com/Z3Prover/z3). On debian-based
systems, this can be done via `sudo apt-get install z3`.

## Usage

To compile a C2PO file, run the `c2po.py` script. For instance, to run an example with the
Booleanizer frontend and using a simulated trace file to map input signals:

    python3 c2po.py -bz --trace ../examples/cav.csv ../examples/cav.c2po 

The assembled binary is generated at `spec.bin` by default and is ready to be run by a properly
configured R2U2 over input data. For full compiler options:

    python3 c2po.py -h

## Input Files

C2PO supports input files written in its custom input language and and in the MLTL standard format.
C2PO input files must have the `.c2po` file extension and MLTL files must have the `.mltl`
extension. See the `../examples/` and `test/` directories for sample files in both formats.

## Signal Mapping

To generate an R2U2-readable binary, C2PO must be given a mapping for variable names to indices in
the signal vector given to R2U2 during runtime. If given an MLTL file as input, the signals will be
mapped to whatever number is in the variable symbol. If given a C2PO file as input, then you must
also provide one of two files to define a mapping:

### Map File

A signal map file has a `.map` file extension and directly associates an index with a variable
symbol. Each line of the input file should be of the form `SYMBOL ':' NUMERAL` such that if `SYMBOL`
corresponds to a signal identifier in the C2PO file, its signal index is set to the integer value of
`NUMERAL`. Note that if `SYMBOL` is not present in the C2PO file, the line is ignored. 

See `test/default.map` for an example.

### CSV File

A CSV trace file given to C2PO as input has a `.csv` file extension and may represent simulated data
to run R2U2 offline. The file requires a header denoted with a '#' character as the first character
of the line. 

See `../examples/cav.csv` for an example.

## Testing

To run C2PO's test suite, see `test/README.md`.

## Stats Format String

C2PO supports outputting stats via a format string with the `--stats` option. The following are the valid specifiers in the format string:

- %F = Input filename
- %S = Total SCQ size
- %sr = SMT solver result
- %se = SMT encoding time
- %st = SMT solver time
- %sn = SMT solver number of calls
- %ee = Eqsat encoding time
- %et = Eqsat solver time
- %eq = Eqsat equivalence result
- %eq = Eqsat equivalence time
- %es = Eqsat equivalence solver time
- %ed = Eqsat equivalence encoding time

For example, to report some statistics from a satisfiability check:

    python3 c2po.py -c --check-sat --stats "%sr,%se,%st" test/sat/sat_5.mltl
