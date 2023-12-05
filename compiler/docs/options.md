# C2PO CLI Options
The following is the usage of C2PO:

    usage: r2u2prep.py [-h] [-q] [--implementation IMPLEMENTATION]
                   [--output-file OUTPUT_FILE] [--int-width INT_WIDTH] [--int-signed]
                   [--float-width FLOAT_WIDTH] [--atomic-checker] [--booleanizer]
                   [--disable-cse] [--extops] [--disable-rewrite]
                   [--disable-assemble] [--mission-time MISSION_TIME]
                   mltl sigs

## Positional Arguments:
    mltl                  file where mltl formula are stored
    sigs                  csv or map file where variable names are mapped to memory
                            locations

## Optional Arguments:
    -h, --help            show this help message and exit
    -q, --quiet           disable output
    --implementation IMPLEMENTATION
                            target R2U2 implementation version (one of 'c', 'c++',
                            'vhdl')
    --output-file OUTPUT_FILE
                            location where output file will be generated
    --int-width INT_WIDTH
                            bit width for integer types
    --int-signed          set int types to signed
    --float-width FLOAT_WIDTH
                            bit width for floating point types
    --atomic-checker      enable atomic checkers
    --booleanizer         enable booleanizer
    --disable-cse         disable CSE optimization
    --extops              enable extended operations
    --disable-rewrite     disable MLTL rewrite rule optimizations
    --disable-assemble    disable assembly generation
    --mission-time MISSION_TIME
                            define mission time (overriding any inference from a
                            simulated input trace)