# R2U2 Test Suite

The R2U2 test suite is intended to test a given `r2u2prep.py` script and `r2u2` binary. Each test case in a suite has an MLTL specification, a trace, and an oracle. The test script compiles the MLTL specification using the given `r2u2prep.py` script, runs the given `r2u2` binary over the compiled specification and trace, and compares the output to the oracle.

## Usage

To run the test suite, run the `r2u2test.py` script as follows:
```bash
python r2u2test.py path/to/r2u2prep.py path/to/r2u2bin SUITE1 SUITE2 ...
```
where `path/to/r2u2prep.py` is the relative or absolute path to the r2u2prep.py script to use for compiling specifications, `path/to/r2u2bin` is the relative or absolute path to the r2u2 binary to run, and `SUITE1 SUITE2 ...` is a non-empty list of suite names to run.

An example command to run the regression test suite from the top-level `r2u2/` directory is as follows:
```bash
python test/r2u2test.py compiler/r2u2prep.py monitors/static/build/r2u2 regression
```
assuming that the C version of the `r2u2` binary has been built. The test results can be seen in the `test/results` directory by default.

## Suites

The JSON files in the `test/suites` directory correspond to the available suites. Some available suites are:
- `ft_subset`
- `pt_subset`
- `regression`

## Adding New Suites

To add a new suite, it is likely easiest to build off of an existing JSON configuration file. The structure of the JSON files is as follows:

```json
{
    "suite": SUITE_NAME,
    "options": {
        "compiler-option": COMPILER_OPTION_VALUE
    },
    "tests": [
        {
            "name": TEST_NAME,
            "mltl": MLTL_FILENAME,
            "trace": TRACE_FILENAME,
            "oracle": ORACLE_FILENAME,
            "options": {
                "compiler-option": COMPILER_OPTION_VALUE
            }
        }
    ]
}
```

where `SUITE_NAME` should be the same as the name of the JSON file (minus the .json extension), `options` is an object corresponding to the CLI options given to the compiler (these options can be overridden for individual tests), `tests` is an array of objects that describe test cases. 

The test cases require a `name`, an `mltl` filename that existsin in `test/mltl`, a `trace` filename that exists in `test/trace`, and an `oracle` filename that exists in `test/oracle`.