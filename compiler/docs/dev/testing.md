# Testing

## Usage

To run the full test suite, simply execute:

    python3 test/test.py

To run a specific set of tests, pass the set name into the `test.py` script:

    python3 test/test.py type-check

To skip one or more subsets when running all tests:

    python3 test/test.py --disable-subset eqsat --disable-subset sat

For a complete list of subsets and tests, see `test/config.json`.

## Configuration

The configuration is stored in `test/config.json`. It is a JSON object whose keys are subset names.
Each subset is a list of tests.

```json
{
  "subset-name": [
    {
      "script": "path/to/script.cmd",
      "output": "path/to/output.expect"
    },
    {
      "spec": "path/to/input.c2po",
      "options": ["--check-sat", "--smt-encoding", "uflia"],
      "output": "path/to/output.expect"
    }
  ]
}
```

### Test Modes

- `script` test: runs `python3 c2po.py --script <script>`
- `spec` test: runs `python3 c2po.py --spec <spec> [options...]`

In both cases, stdout+stderr are captured and compared against the `output` expectation file via a
unified diff.
