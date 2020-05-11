# R2U2 Dependencies: 
- Posix environment (Linux, MacOS, Etc.)
- Python3 (version 3.6 or greater)
- Python Lex & Yacc (`python3 -m pip install —user —upgrade  ply`)
- C99 std compiler (gcc or clang)
- Make

# MLTL Formula Syntax

Note that MLTL formulas are terminated by semicolons (;). Additionally, parentheses may be used to explicitly specify operator precidence. Also note that if you are entering formulas directly into the command line, use single quotes (') around the entire formula, or string of formulas. 

| **Expression** | **Syntax**  |
|----------------|-------------|
| Negation       |    `!E1;`    |
| Conjunction    |  `E1 & E2;`  |
| Disjunction    |  `E1 \| E2;`  |
| Implication    |  `E1 -> E2;` |
| Equivalence    | `E1 <-> E2;` |
| Globally       | `G[ti,tf] E1;` or `G[tf] E1;`|
| Future         | `F[ti,tf] E1;` or `F[tf] E1;`|
| Until          | `E1 U[ti,tf] E2;` or `E1 U[tf] E2;`|
| Historically   | `H[ti,tf] E1;` or `H[tf] E1;`|
| Once           | `O[ti,tf] E1;` or `O[tf] E1;`|
| Since          | `E1 S[ti,tf] E2;` or `E1 S[ti,tf] E2;`|

# Instructions for running the C version of R2U2

1. Compile R2U2's temporal logic engine using the `make` command.

2. To convert formulas to binary files for R2U2, run the *r2u2prep.py* script. Users may select to either to enter formulas manually from the command line or point to a valid *.mltl* file. 

    `./r2u2prep [formula or path to a formula file]`
    
    - **Note:** This script will point the user to the newly made **tools/binary_files** directory, where the binary files are located.
    - **Note:** All mixed past-time and future-time formulas will be ignored, since R2U2 cannot guarantee the correctness of these mixed-type formulas.   
    
    
3. To run R2U2, execute:

    `./bin/r2u2 tools/binary_files [the path to a time series, Boolean input .csv file]`.

    - **Note**: If an input file is excluded from this command, then R2U2 looks to the command line for Boolean inputs, separated by commas. Time steps are separated by pressing `Enter`.

4. The output to R2U2 is saved in the *R2U2.log* file. For runs of R2U2 with more than one formula, it may be useful to split this file into multiple result files with one formula in each file. In the **tools/** directory, there is a bash script *split_verdicts.sh* which does this. To execute, run `./split_verdicts [R2U2 log file]`.
    - **Note:** This script names formula files with the notation *[original file name]_formula\#.txt*, where \# is the corresponding formula number, indexed from 1.