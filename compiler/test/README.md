# C2PO Test Suite

## Usage

To run the full test suite, simply execute:

    python3 test.py

To run a specific set of tests, pass the set name into the `test.py` script:

    python3 test.py type_check

For a complete list of tests and test sets, see `config.json`

## Configuration

The configuration for tests is stored in `config.json`. This file is a JSON object whose members are
test sets. Each test set is a list of tests, with each test providing an input script and a file
that stores expected output.

```json
{
    "test_set_name": [
        {
            "script": "path/to/script.cmd",
            "output": "path/to/output.expect",
        }
    ]
}
```

Upon executing `"script"`, the test script compares the combined stdout and stderr of the `c2po.py`
call to the contents of the argument to `"output"`.

The script assumes that `z3` and `egglog` are in `PATH`. To add these to `PATH` (assuming they are
installed in `compiler/deps`):

    export PATH=$PATH:/path/to/r2u2/compiler/deps/z3/bin
    export PATH=$PATH:/path/to/r2u2/compiler/deps/egglog/target/release
