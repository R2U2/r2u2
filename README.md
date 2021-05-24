# R2U2 Dependencies:
- Posix environment (Linux, MacOS, Etc.)
- Python3 (version 3.6 or greater)
- Python Lex & Yacc (`python3 -m pip install —user —upgrade  antlr4-python3-runtime `)
- C99 std compiler (gcc or clang)
- Make


# MLTL Formula Syntax
Formula files contain one or more lines of temporal formulas: one per line and each line terminating with a semi-colon (;). Each formula can contain either future-time MLTL or past-time MLTL operators along with the supported set of propositional logic. R2U2 does not support mixed-tense formulas. Additionally, parentheses may be used to explicitly specify operator precidence. Note that if you are entering formulas directly into the command line, use single quotes (') around the entire formula, or string of formulas.

| **Expression** |               **Syntax**            |
|----------------|-------------------------------------|
| Negation       |                 `!E1;`              |
| Conjunction    |               `E1 & E2;`            |
| Disjunction    |               `E1 | E2;`            |
| Implication    |               `E1 -> E2;`           |
| Equivalence    |              `E1 <-> E2;`           |
| Globally       |    `G[ti,tf] E1;` or `G[tf] E1;`    |
| Future         |    `F[ti,tf] E1;` or `F[tf] E1;`    |
| Until          | `E1 U[ti,tf] E2;` or `E1 U[tf] E2;` |
| Historically   |    `H[ti,tf] E1;` or `H[tf] E1;`    |
| Once           |    `O[ti,tf] E1;` or `O[tf] E1;`    |
| Since          |             `E1 S[ti,tf] E2;`       |


# Input Trace:
An input trace is a CSV file with one column per Boolean input and one row per time-step. In the formula the inputs are written as "a#" where "#" is the zero-indexed column number, from left to right. In the following example, the value of a0 is 1, 0, 1 and the value of a1 is 0, 0, 1.
```
1,0
0,0
1,1
```


# Verdict Output:
Verdicts are output one per line as the formula id number (indexing from 1), followed by a colon and then the verdict tuple. The verdict tuple consists of an integer timestamp and a literal "T" or "F" to mark the truth value. The asynchronous monitors produce *aggregated output* — that is, if they can determine a range of values with the same truth at once, only the last time is output. In the example below, formula with ID 2 is false from time 8-11 inclusive.
```
2:7,T
5:4,F
2:11,F
```


# Optional Features:
The TL engine uses a0-an to refer to the nth boolean of the trace. Aliasing human-friendly names to these in the formula file will be supported with inclusion of the signal processing layer in the targetted v2.0 release. Additionally, you may optionally run a bash command (see instruction \#4 below) to separate R2U2's output file into individual formula files, if that is easier for your post-processing. An is provided in the 'tools' directory. Note that the formula numbers are associated with their given line number in the *.mltl file.


# Instructions for running the C version of R2U2
1. Compile R2U2's temporal logic engine using the `make` command.

2. To convert formulas to binary files for R2U2, run the *r2u2prep.py* script. Users may select to either to enter formulas manually from the command line or point to a valid *.mltl* file.

    `./r2u2prep.py [formula or path to a formula file]`
    - **Note:** This script will point the user to the newly made **tools/binary_files** directory, where the binary files are located.
    - **Note:** All mixed past-time and future-time formulas will be ignored,
3. To run R2U2, execute:

    `./bin/r2u2 tools/binary_files [the path to a time series, Boolean input .csv file]`.
    - **Note**: If an input file is excluded from this command, then R2U2 looks to the command line for Boolean inputs, separated by commas. Time steps are separated by pressing `Enter`. To exit this input mode, send end-of-file (EOF), which can be done with `ctrl-d`.
    - **Memory bounds:** R2U2 is designed for use in a flight software environment without memory allocation; therefore, memory bounds are set at compile time based on the settings in *src/R2U2Config.h*. Some values that may require adjustment depending on the size of the formulas; please contact us if you have any issues with the default configuration.

4. The output to R2U2 is saved in the *R2U2.log* file. For runs of R2U2 with more than one formula, it may be useful to split this file into multiple result files with one formula in each file. In the **tools/** directory, there is a bash script *split_verdicts.sh* which does this. To execute, run

    `./tools/split_verdicts [R2U2 log file]`.
    - **Note:** This script names formula files with the notation `[original file name]_formula\#.txt`, where \# is the corresponding formula number, indexed from 1.