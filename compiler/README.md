# C2PO

C2PO (Configuration Compiler for Property Organization) is the formula compiler for R2U2.

## Requirements

C2PO requires Python 3.8 or newer.

To enable equality saturation, first install `cargo` and `make`. To install `cargo`, follow the
instructions here: https://www.rust-lang.org/tools/install. To install `make` on a debian-based
system, run `sudo apt-get install build-essential`. Then run the `setup_egglog.sh` script.

To enable satisfiability checking, install Z3. On debian-based systems, this can be done via `sudo
apt-get install z3`.

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

