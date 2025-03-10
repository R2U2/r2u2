# CLI Options
The following is the usage of C2PO:

    usage: c2po.py [-h] [--trace TRACE] [--map MAP] [-q] [--debug [DEBUG]] [--stats] [--impl {c,cpp,vhdl}] [-o OUTPUT] [--int-width INT_WIDTH]
               [--int-signed] [--float-width FLOAT_WIDTH] [--mission-time MISSION_TIME] [--endian {native,network,big,little}] [-at] [-bz] [-p] [-tc]
               [-c] [-dc] [-dr] [--extops] [-nnf] [-bnf] [-eq] [-sat] [--timeout-eqsat TIMEOUT_EQSAT] [--timeout-sat TIMEOUT_SAT]
               [--write-c2po [WRITE_C2PO]] [--write-mltl [WRITE_MLTL]] [--write-prefix [WRITE_PREFIX]] [--write-pickle [WRITE_PICKLE]]
               [--write-smt [WRITE_SMT]] [--copyback COPYBACK]
               mltl

## Positional Arguments:
    mltl                  file where mltl formula are stored

## Optional Arguments:
    -h, --help            show this help message and exit
    --trace TRACE         CSV file where variable names are mapped to signal order using file header
    --map MAP             map file where variable names are mapped to signal order
    -q, --quiet           disable output
    --debug [DEBUG]       set debug level (0=none, 1=basic, 2=extra)
    --stats               enable stat output
    --impl {c,cpp,vhdl}   specifies target R2U2 implementation version (default: c)
    -o OUTPUT, --output OUTPUT
                            specifies location where specification binary will be written
    --int-width INT_WIDTH
                            specifies bit width for integer types (default: 32)
    --int-signed          specifies signedness of int types (default: true)
    --float-width FLOAT_WIDTH
                            specifies bit width for floating point types (default: 32)
    --mission-time MISSION_TIME
                            specifies mission time, overriding inference from a trace file, if present
    --endian {native,network,big,little}
                            Specifies byte-order of spec file (default: little)
    -bz, --booleanizer    enable booleanizer
    -p, --parse           only run the parser
    -tc, --type-check     only run the parser and type checker
    -c, --compile         only run the parser, type checker, and passes
    -dc, --disable-cse    disable CSE optimization
    -dr, --disable-rewrite
                            disable MLTL rewrite rule optimizations
    --extops              enable extended operations
    -nnf                  enable negation normal form
    -bnf                  enable boolean normal form
    -eq, --eqsat          enable equality saturation
    -sat, --check-sat     enable satisfiability checking of future-time formulas
    --timeout-eqsat TIMEOUT_EQSAT
                            set the timeout of equality saturation calls in seconds (default: 3600)
    --timeout-sat TIMEOUT_SAT
                            set the timeout of sat calls in seconds (default: 3600)
    --write-c2po [WRITE_C2PO]
                            write final program in C2PO input format
    --write-mltl [WRITE_MLTL]
                            write final program in MLTL standard format
    --write-prefix [WRITE_PREFIX]
                            write final program in prefix notation
    --write-pickle [WRITE_PICKLE]
                            pickle the final program
    --write-smt [WRITE_SMT]
                            write SMT SAT encoding of FT formulas
    --copyback COPYBACK   name of directory to copy workdir contents to upon termination