# Instructions for running the C version of R2U2

1. Run the `make` command to compile R2U2's temporal logic engine.

2. To convert formulas to binary files for R2U2, run the *r2u2prep.py* script. Users may select to either to enter formulas manually from the command line or point to a valid *.mltl* file.

`./r2u2prep [formula or formula file]`

This script will point the user to the newly made *tools/binary_files* directory, where the binary files are located.

3. To run R2U2, execute `./bin/r2u2 tools/binary_files [time series, Boolean input .csv file]`.
    * Note that if an input file is excluded from this command, then R2U2 looks to the command line for Boolean inputs, separated by commas.