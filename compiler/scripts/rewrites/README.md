# EQSat Rewrite Pipeline

Scripts for proving correctness of MLTL rewrite rules and generating egglog
files for equality saturation.

## Files

- `rewrites.json` — rewrite schemas in the standard JSON format
- `prepare.sh` — shared dependency: `rewrites.json` → `equiv/`
- `prove_rewrites.sh` — prepare → smt2 → prove
- `generate_egg.sh` — prepare → egglog rewrite files
- `generate_latex_table.py` — optional LaTeX table export from rewrite JSON
- `equiv/`, `smt2/` — generated proof obligations

Shared generators live in the parent `scripts/` directory
(`generate_equiv_files.py`, `generate_smt2_equiv.sh`, `prove.sh`,
`generate_egglog.py`).

## Run

Requires `cvc5` and `z3` on `PATH` for the prove step.

```bash
./prepare.sh                              # refresh equiv/
./prove_rewrites.sh [timeout] [jobs]      # defaults: 60s, 8 jobs
./generate_egg.sh                         # write temporal/const_folding/extended.egg
```

`prove_rewrites.sh` and `generate_egg.sh` each call `prepare.sh` first, so either
can be run alone after editing `rewrites.json`.

Outputs land under `../../c2po/egglog/rewrites/`. Each generated `.smt2` file
encodes the *negation* of a rewrite's equivalence, so `UNSAT` means the rewrite
is valid.

## Manual steps

If you edit `rewrites.json`:

```bash
python3 ../generate_equiv_files.py rewrites.json equiv/
../generate_smt2_equiv.sh equiv/ smt2/ ../../c2po.py
../prove.sh smt2/
PYTHONPATH=../.. python3 ../generate_egglog.py \
  equiv/ rewrites.json ../../c2po/egglog/rewrites
```
