# R2U2 Dependencies: 
* Posix environment (Linux, MacOS, Etc.)
* Python3 (version 3.6 or greater)
* Python Lex & Yacc (python3 -m pip install —user —upgrade  ply)
* C99 std compiler (gcc or clang)
* Make

# Instructions for running the C version of R2U2

1. Compile R2U2's temporal logic engine using the `make` command.

2. To convert formulas to binary files for R2U2, run the *r2u2prep.py* script. Users may select to either to enter formulas manually from the command line or point to a valid *.mltl* file.

`./r2u2prep [formula or formula file]`

This script will point the user to the newly made *tools/binary_files* directory, where the binary files are located.

| **Expression** | **Syntax**  |
|----------------|-------------|
| Negation       |    `!E1`    |
| Conjunction    |  `E1 & E2`  |
| Disjunction    |  `E1 | E2`  |
| Implication    |  `E1 -> E2` |
| Equivalence    | `E1 <-> E2` |
-----------------|-------------|
| Globally       | `G[ti,tf] E1` or `G[tf] E1`|
| Future         | `F[ti,tf] E1` or `F[tf] E1`|
| Until          | `E1 U[ti,tf] E2` or `E1 U[tf] E2`|
-----------------|-------------|
| Historically   | `H[ti,tf] E1` or `H[tf] E1`|
| Once           | `O[ti,tf] E1` or `O[tf] E1`|
| Since          | `E1 S[ti,tf] E2` or `E1 S[ti,tf] E2`|
-----------------|-------------|
| 
3. To run R2U2, execute `./bin/r2u2 tools/binary_files [time series, Boolean input .csv file]`.
    * Note that if an input file is excluded from this command, then R2U2 looks to the command line for Boolean inputs, separated by commas.