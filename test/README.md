# Test Suite

The R2U2 test suite is intended to test `c2po.py` and `r2u2`. Each test case in a suite has an MLTL/ptMLTL
specification, a trace, and an oracle. The test script compiles the MLTL/ptMLTL specification using the
given `c2po.py` script, runs the given `r2u2` binary over the compiled specification and trace, and
compares the output to the oracle.

The tests also include a "hyper tester" that tests R2U2 over all possible traces for variations of a
given formula. This test will likely take a long time on a personal machine (>1 hour) to complete.

## Usage

To run the test suite, run the `r2u2test.py` script as follows:
```bash
python3 r2u2test.py --c2po path/to/c2po.py --monitor implementation --r2u2 path/to/r2u2bin SUITE1 SUITE2 ...
```
where `path/to/c2po.py` is the relative or absolute path to the c2po.py script to use for compiling
specifications, `implementation` indicates the `c` or `rust` implementation of R2U2, and `path/to/r2u2bin` is the relative or absolute path to the r2u2 binary or Cargo.toml file to run, and
`SUITE1 SUITE2 ...` is a non-empty list of suite names to run.

An example command to run the regression test suite on the C implementation from the top-level `r2u2/` directory is as
follows:
```bash
python3 test/r2u2test.py --c2po compiler/c2po.py --monitor c --r2u2 monitors/c/build/r2u2 regression
```
assuming that the C version of the `r2u2` binary has been built.

An example command to run the regression test suite on the Rust implementation from the top-level `r2u2/` directory is as
follows:
```bash
python3 test/r2u2test.py --c2po compiler/c2po.py --monitor rust --r2u2 monitors/rust/r2u2_cli/target/release/r2u2_cli regression
```
assuming that the Rust release version of the `r2u2` binary has been built.

The test results can be seen in the `test/results` directory by default.

Use the `--copyback` option to copy all the files used in the test case to the results directory.
This is useful for re-running and debugging specific test cases.

To run the hyper tester, install all the python requirements via `pip install -r requirements.txt`
then run via `python3 hyper_test.py --monitor c` or `python3 hyper_test.py --monitor rust` to test the C version and Rust version of R2U2, respectively.

## Suites

The JSON files in the `test/suites` directory correspond to the available suites. Some available
suites are:
- `ft_subset`
- `pt_subset`
- `regression`
- `cav`
- `all` (runs every suite in `test/suites`)

## Adding New Suites

To add a new suite, it is easiest to build off of an existing JSON configuration file. The structure
of the JSON files is as follows:

```json
{
    "suite": "SUITE_NAME",
    "options": {
        "compiler-option": "COMPILER_OPTION_VALUE"
    },
    "tests": [
        {
            "name": "TEST_NAME",
            "mltl": "MLTL/ptMLTL_FILENAME",
            "trace": "TRACE_FILENAME",
            "oracle": "ORACLE_FILENAME",
            "options": {
                "compiler-option": "COMPILER_OPTION_VALUE"
            }
        }
    ],
    "suites": [ "SUITE_1", "SUITE_2", "..." ]
}
```

where `"SUITE_NAME"` should be the same as the name of the JSON file (minus the .json extension),
`"options"` is an object corresponding to the CLI options given to the compiler (these options can
be overridden for individual tests), `"tests"` is an array of objects that describe test cases. 

The test cases require a `"name"`, an `"mltl"` filename that exists in in `test/mltl`, a `"trace"`
filename that exists in `test/trace`, and an `"oracle"` filename that exists in `test/oracle`.

Each `"SUITE_N"` in the `"suites"` attribute should be the name of a suite in the `suites/`
directory, where each named suite will be run.