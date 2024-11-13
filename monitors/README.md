# R2U2 Dependencies:
- Posix environment (Linux, MacOS, Etc.)
- Python3 (version 3.6 or greater)
- C99 std compiler (gcc or clang)
- Make

# Instructions for running the C version of R2U2
1. Compile R2U2 by running the `make` command in the 'monitor' directory.

    - To run the default test suite, use the `test_all.sh` script from inside the top level `test` directory, after running `make`.

2. To convert formulas to specification files for R2U2, run the *r2u2prep.py* script found inside the `compiler` directory.

3. To run R2U2, execute:

    `r2u2/monitor/build/r2u2 [the path to a r2u2_spec.bin file] [the path to a time series input .csv file]`.
    - **Note**: If an input file is excluded from this command, then R2U2 looks to the command line for inputs, separated by commas. Time steps are separated by pressing `Enter`. To exit this input mode, send end-of-file (EOF), which can be done with `ctrl-d`.
    - **Memory bounds:** R2U2 is designed for use in embedded control environments (like flight software) without memory allocation; therefore, memory bounds are set at compile time based on the settings in *src/internals/bounds.h*. Some values that may require adjustment depending on the size of the formulas; please contact us if you have any issues with the default configuration.

4. The output to R2U2 is saved in the *R2U2.log* file. For runs of R2U2 with more than one formula, it may be useful to split this file into multiple result files with one formula in each file. In the **tools/** directory, there is a bash script *split_verdicts.sh* which does this. To execute, run

    `./tools/split_verdicts [R2U2 log file]`.
    - **Note:** This script names formula files with the notation `[original file name]_formula\#.txt`, where \# is the corresponding formula number, indexed from 0.

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