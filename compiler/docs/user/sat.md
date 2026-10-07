# Satisfiability Checking

C2PO encodes future-time MLTL as SMT-LIB2 and asks an external solver whether a formula has a
satisfying trace. Use `check_sat` after `desugar`. The command checks each future-time specification,
then the conjunction of those specifications when the program contains more than one. Contracts are
skipped.

`check_sat` looks for an SMT-LIB2 solver on `PATH`, in this order: `z3`, `cvc5`, `yices-smt2`,
`mathsat`, `bitwuzla`. For the `uflia` and `qf_uflia` encodings, `cvc5` is invoked with
`--finite-model-find` and `--fmf-bound`.

## From the CLI

`--check-sat` runs a non-strict check and prints each result. `--compile` stops before assembly when
you only want the SAT result:

    python3 c2po.py --spec test/sat/sat_5.mltl --check-sat --compile

Related options:

- `--smt-encoding {uflia,qf_uflia,qf_bv,uf}` selects the encoding (default: `uflia`)
- `--smt-max-time` is the solver timeout in seconds (default: `5`)
- `--smt-max-memory` is the solver memory limit in MB (`0` means no limit)

For a `.c2po` file whose inputs are not Boolean, pass `-bz` so the booleanizer runs before
type checking. `qf_bv` and `uf` accept Boolean inputs only.

## Script and Interactive Mode

`check_sat` requires a desugared program. A minimal script (`run_sat.cmd`):

    parse_mltl test/sat/sat_5.mltl
    type_check
    desugar
    check_sat uf --no-strict --print --smt-max-time 20

Run it with:

    python3 c2po.py --script run_sat.cmd

For a `.c2po` file, call `enable_booleanizer` before `type_check` when the specification uses
non-Boolean signals.

`check_sat` options:

- `theory` (required): `uflia`, `qf_uflia`, `qf_bv`, or `uf`
- `--strict` / `--no-strict` (default: non-strict)
- `--print` / `--no-print` (default: do not print). With `--print`, each specification is reported as
  `<name> : <result>`. A multi-specification program also prints `program : <result>`.
- `--smt-max-time` (default: `5`)
- `--smt-max-memory` (default: `0`)

Without `--print`, `unsat` and `unknown` are reported as warnings.

## Encodings

| Theory | SMT-LIB logic | Fragment |
| --- | --- | --- |
| `uflia` | `UFLIA`, or `UFNIA` when the formula uses multiplication, division, or modulo | Boolean and integer signals. Supports symbolic interval bounds. `G` and `F` are quantified. |
| `qf_uflia` | `QF_UFLIA`, or `QF_UFNIA` when arithmetic is nonlinear | Boolean and integer signals. `G`, `F`, `U`, and `R` are unrolled. Symbolic bounds are rejected. Wide nested intervals produce large queries. |
| `qf_bv` | `QF_BV` | Boolean signals only. Temporal operators are encoded with bit-vector shifts of width `wpd + 1`. Symbolic bounds are rejected. |
| `uf` | `QF_UF` | Boolean signals. Integer equality is encoded with an uninterpreted `Value` sort. Ordered comparisons (`<`, `<=`, `>`, `>=`), arithmetic, symbolic bounds, and past-time operators are rejected. Boolean `&`, `|`, `^`, and `~` are encoded as logical connectives. |

`uf` is the slack-function translation of Hariharan et al., FORMATS 2023. Each non-atomic
subformula gets an uninterpreted slack function, and accumulated interval bounds decide the times at
which that slack is constrained. The query itself uses only uninterpreted functions and Boolean
connectives.

## Strict and Non-strict

The default is non-strict (`--no-strict`). The trace is assumed long enough to cover the formula:
UFLIA uses the computed propagation length, QF_UFLIA uses `wpd + 1` (an atom has `wpd` 0 and still
needs a one-step trace), and `uf` follows the FORMATS encoding.

`--strict` asks whether a trace of any length satisfies the formula. On a short trace, `G` and `R`
may hold vacuously, while `F` and `U` do not. The CLI `--check-sat` path is always non-strict; pass
`--strict` from a script or the REPL.

## Results

A completed check is one of:

- `sat`: some trace satisfies the formula
- `unsat`: no trace satisfies the formula
- `unknown`: the solver finished without deciding

`timeout`, `memout`, and `fail` mean the solver did not return a verdict. `check_sat` then exits
with an error. `fail` includes a solver process that was killed (for example, by the OS) rather than
exiting with an out-of-memory message.

## Writing the SMT Query

`write_smt_encoding` writes the same query `check_sat` would solve, without invoking a solver:

    write_smt_encoding out/spec.smt2 uf --no-strict
    write_smt_encoding out/spec.smt2 uflia --formula MySpec

One formula is written to the given path. Several formulas are written as `<symbol>.smt2` files in
the given directory.

Examples live in `test/sat/`.
