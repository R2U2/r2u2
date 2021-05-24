# R2U2 Dependencies:
- Posix environment (Linux, MacOS, Etc.)
- Python3 (version 3.6 or greater)
- Python Lex & Yacc (`python3 -m pip install —user —upgrade  antlr4-python3-runtime `)
- C99 std compiler (gcc or clang)
- Make


# Instructions for running the C version of R2U2
1. Compile R2U2'by running the `make` command in the 'R2U2_C' directory.

    - To run the default test suite, use the `test_all.sh` script from inside the top level `test` directory, after compiling R2U2_C.

2. To convert formulas to specification files for R2U2, run the *r2u2prep.py* script found inside the `tools` directory. Users may select to either to enter formulas manually from the command line or point to a valid *.mltl* file.

    `python3 tools/r2u2prep.py [formula or path to a formula file]`
    - **Note:** This script will point the user to the newly made **tools/gen_files/binary_files** directory, where the specification binary files are located.
    - **Note:** A formula file may have both past and future tense formulas; however, all formulas mixing past-time and future-time operators will be ignored. 
3. To run R2U2, execute:

    `.R2U2_C/bin/r2u2 tools/gen_files/binary_files [the path to a time series input .csv file]`.
    - **Note**: If an input file is excluded from this command, then R2U2 looks to the command line for inputs, separated by commas. Time steps are separated by pressing `Enter`. To exit this input mode, send end-of-file (EOF), which can be done with `ctrl-d`.
    - **Memory bounds:** R2U2 is designed for use in embedded control environments (like flight software) without memory allocation; therefore, memory bounds are set at compile time based on the settings in *src/R2U2Config.h*. Some values that may require adjustment depending on the size of the formulas; please contact us if you have any issues with the default configuration.

4. The output to R2U2 is saved in the *R2U2.log* file. For runs of R2U2 with more than one formula, it may be useful to split this file into multiple result files with one formula in each file. In the **tools/** directory, there is a bash script *split_verdicts.sh* which does this. To execute, run

    `./tools/split_verdicts [R2U2 log file]`.
    - **Note:** This script names formula files with the notation `[original file name]_formula\#.txt`, where \# is the corresponding formula number, indexed from 0.


# MLTL Formula Syntax
Formula files contain one or more lines of temporal formulas: one per line and each line terminating with a semi-colon (;). Each formula can contain either future-time MLTL or past-time MLTL operators along with the supported set of propositional logic. R2U2 does not support mixed-tense formulas. Additionally, parentheses may be used to explicitly specify operator precedence. Note that if you are entering formulas directly into the command line, use single quotes (') around the entire formula, or string of formulas.

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

# Atomic Checker Syntax
Following the temporal formulas in the formula files, atomic checker expressions may be included to .
The full syntax of an AT checker expression is:

`ATOM := FILTER(SIGNAL,[CONSTANT]) CONDITIONAL CONSTANT|SIGNAL;` where  
**ATOM** is a name appearing in the temporal logic formulas above.  
**FILTER** is a filter to apply to a stream of data (signal) from the set in the table below.  
**SIGNAL** is in the form 'sN' where N is a natural number in the set [0,255] corresponding to the desired index in the input data stream.  
**CONSTANT** is an integer that can be represented as a 32 bit signed integer.  
**CONDITIONAL** is a comparison operator in the set [==, !=, <, >, <=, >=].

|         **Filter**         |       **Syntax**       |
|----------------------------|------------------------|
| Boolean                    | `bool(s)`              |
| Integer                    | `int(s)`               |
| Floating Point             | `float(s)`             |
| Rate                       | `rate(s)`              |
| Absolute difference angle  | `abs_diff_angle(s, c)` |
| Rolling average            | `movavg(s,c)`          |

In the filter syntax, `s` is a **SIGNAL** and `c` is a **CONSTANT**.

### Examples
`a5 := abs_diff_angle(s3,105) < 50;` checks if the absolute difference between the data of signal 3 and the value 105 when treated as angles is below 50.  
`a43 := int(s32) == s33;` checks that the values of signals 32 and 33 are in agreement when treated as integers.

As a default case, atoms of the format 'a#' where '#' is an integer will be interpreted as the boolean value of the '#-th' column without needing to be declared. See the input trace section for an example.


# Input Trace:
An input trace is a CSV file with one column per input and one row per time-step. In the following example, the value of the default atomic a0 is 1, 0, 1 and the value of a1 is 0, 0, 1.
```
1,0
0,0
1,1
```


# Verdict Output:
Verdicts are output one per line as the formula id number (indexing from 0), followed by a colon and then the verdict tuple. The verdict tuple consists of an integer timestamp and a literal "T" or "F" to mark the truth value. The asynchronous monitors produce *aggregated output* — that is, if they can determine a range of values with the same truth at once, only the last time is output. In the example below, formula with ID 2 is false from time 8-11 inclusive.
```
2:7,T
5:4,F
2:11,F
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
