# R2U2 Front End Selection

R2U2 execution is split across TL and Booleanizer (BZ) engines. C2PO controls this through context
settings and expression typing.

## Booleanizer Behavior

The Booleanizer is required for non-boolean computation in formulas, including:

- arithmetic and bitwise expressions
- relational operators over non-bool values
- parameterized set aggregation (`foratleast`, `foratmost`, `forexactly`)
- `prev(...)` over non-trivial expressions

If the Booleanizer is disabled and non-boolean operations are present, type checking fails with an
explicit error.

## How It Is Enabled

- CLI: `-bz` / `--booleanizer`
- REPL/script: `enable_booleanizer` and `disable_booleanizer`

Without the Booleanizer, purely boolean specifications can still compile and run through the TL path.
