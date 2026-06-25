# Formula Equivalence Checking

C2PO supports equivalence checking between formulas using SMT via the `check_equiv` command. This is
primarily used with `.equiv` input files parsed with `parse_equiv` in REPL/script mode.

`check_equiv` checks formulas **pairwise in order**: `(f0,f1)`, `(f1,f2)`, `(f2,f3)`, etc.
It prints one summary result:

- `equiv`: all checked adjacent pairs are equivalent
- `not-equiv`: at least one checked pair is not equivalent
- `unknown`: no pair was proven non-equivalent, but at least one check was inconclusive (e.g., timeout)

## `.equiv` File Format (Brief)

A `.equiv` file contains:

- zero or more optional constraint lines starting with `c:`
- one MLTL formula per line

Supported temporal operators are `G`, `F`, `U`, and `R`.  
Atomic signal names are `a0`, `a1`, ... and boolean proposition variables are `p0`, `p1`, ...

Minimal example:

    c: b0 >= 0
    c: b1 >= b0
    G[0,b0] a0
    !F[0,b0] !a0
    (a0 U[0,b1] a1)

Notes:

- `b0`, `b1`, ... are symbolic interval bounds.
- `M` is available as mission time in constraints.
- End each formula with a newline (the parser expects line-based formulas).

## Running Equivalence Checks

Script-mode example, assuming the minimal example above is written to demo.equiv (`run_equiv.cmd`):

    parse_equiv demo.equiv
    desugar
    check_equiv uflia --smt-max-time 5 --smt-max-memory 0

Run it with:

    python3 c2po.py --script run_equiv.cmd

You can also emit the SMT encodings used for equivalence by appending the following to `run_equiv.cmd`:

    write_equiv_smt_encoding out/equiv_smt uflia
