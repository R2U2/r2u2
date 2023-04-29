# C2PO

C2PO (Configuration Compiler for Property Organization) is the formula compiler for R2U2.

## Usage

C2PO requires an input MLTL file and a file for generating a signal mapping.

To compile an MLTL file, run the `r2u2prep.py` script with a `.csv` or `.map` file as argument. One of the `--booleanizer` or `--atomic-checker` flags must be set. For instance, to run an example:

    python r2u2prep.py --booleanizer examples/cav.mltl examples/cav.csv 

For full compiler options:

    python r2u2prep.py -h

## MLTL File Format

MLTL files are used as input to C2PO and use C2PO's specification language. They include various sections: 

- **INPUT**: Where input signals and their types are declared
- **FTSPEC**: Where future-time MLTL specifications are defined. These specifications will use SCQs for their memory.
- **PTSPEC**: Where past-time MLTL specifications are defined. The specifications will use box queues for their memory.
- **STRUCT**: Where C-like structs are defined.
- **DEFINE**: Where macros can be defined.
- **ATOMIC**: Where atomics used by the atomic checker are defined.

See `syntax.md` for a formal description of the input file format and `examples/` directory for sample files.

## CSV File Format

A CSV file given to C2PO as input has a `.csv` file extension and requires a header denoted with a '#' character as the first character of the line. For instance:

    # sig0,sig1
    0,1

is a valid csv file.

## Signal Map File Format

A signal map file has a `.map` file extension. Each line of the input file should be of the form `SYMBOL ':' NUMERAL` such that if `SYMBOL` corresponds to a signal identifier in the MLTL file, its signal ID is set to the integer value of `NUMERAL`.

Note that if `SYMBOL` is not present in the MLTL file, the line is ignored.