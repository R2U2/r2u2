# C2PO Test Suite

## Usage

To run the full test suite, simply execute:

    python3 test.py

To run a specific set of tests, pass the set name into the `test.py` script:

    python3 test.py type_check

For a complete list of tests and test sets, see `config.json`

## Configuration

The configuration for tests is stored in `config.json`. This file is a JSON object whose members are
test sets. Each test set is a list of tests, with each test providing an input file, a set of
options passed to C2PO, and some sort of expected output.

```json
{
    "test_set_name": [
        {
            "input": "path/to/input.c2po",
            "options": ["list", "of", "c2po", "options"],
            "expected_output": "path/to/output.expect",
            "expected_serialization": "tmp.out"
        }
    ]
}
```

The test script runs `c2po.py` over the input file and options, then compares the output of each
expected file against the generated output:
- `"expected_output"` compares stdout of the `c2po.py` call
- `"expected_serialization"` compares contents of `tmp.out`
