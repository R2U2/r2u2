# Quick-Start Guide

See below sections for the guide for each version of R2U2. 

## Software

### Dependencies

- Posix environment (Linux, MacOS, Etc.)
- Python3 (version 3.6 or greater)
- C99 std compiler (gcc or clang)
- Make

### Using the C Version

The C version of R2U2 is also called the "static" version, since it uses entirely static memory. To monitor a specification over a simulated trace:

1. Compile R2U2 by running the `make` command in the `r2u2/monitors/c` directory:

        cd monitors/c
        make
        cd ../../

    <!-- - To run the default test suite, run `python test/r2u2test.py [suite name]` after compiling `r2u2` where `suite name` is the name of any file in the `test/suites` directory (`regression`, for example). -->

2. Write a specification in C2PO's input format. For example, write the following to a file named `spec.c2po`:

        INPUT
            request, grant: bool;

        FTSPEC
            -- If a request is made, it shall be granted within 5 time steps.
            request -> F[0,5] grant;

3. Write a map file to define the order in which R2U2 will receive the inputs. For example, write the following to `spec.map`:

        request:0
        grant:1

4. Compile the specification using the `r2u2prep.py` script found inside the `compiler/` directory. This script uses C2PO to parse, type check, optimize, and assemble a binary version of the specification for R2U2 to monitor.

        python3 compiler/r2u2prep.py --booleanizer --map spec.map spec.c2po

    - **Note:** This command generates a file `spec.bin` that is a R2U2-readable binary encoding of the specification.

    - **Note:** Internally, R2U2 includes a layer that converts generic input signals to MLTL-compatible atomic propositions. The `--booleanizer` flag denotes that we use the "Booleanizer" engine as this layer.

5. Generate a simulated trace. For example, write the following to `spec.csv`:

        1,0
        0,0
        0,1
        0,0
        1,0
        0,0
        0,0
        0,0
        0,0
        0,0

6. To run R2U2 over this simulated trace, run the command:

        ./monitors/c/build/r2u2 spec.bin spec.csv

    - **Note**: If `spec.csv` is excluded from this command, then R2U2 looks to the command line for inputs, separated by commas. Time steps are separated by pressing `Enter`. To exit this input mode, send end-of-file (EOF), which can be done with `ctrl-d`.

    - **Memory bounds:** R2U2 is designed for use in embedded control environments (like flight software) without memory allocation; therefore, memory bounds are set at compile time based on the settings in *src/R2U2Config.h*. Some values that may require adjustment depending on the size of the formulas; please contact us if you have any issues with the default configuration.

7. The output to R2U2 is printed to stdout and can be redirected into a file for analysis. For runs of R2U2 with more than one formula, it may be useful to split this output into multiple result files with one formula in each file. In the **test/** directory, there is a bash script *split_verdicts.sh* which does this. To execute, run

    `./test/split_verdicts [R2U2 log file]`.

    - **Note:** This script names formula files with the notation `[original file name]_formula\#.txt`, where \# is the corresponding formula number, indexed from 0.
