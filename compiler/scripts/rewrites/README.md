# Rewrite Proofs and Egglog Generation

Scripts for proving MLTL rewrite rules correct and generating egglog files for
C2PO equality saturation.

## Files

- `rewrites.json` — rewrite schemas (includes former FRET rules under `"fret"`)
- `prove_rewrites.sh` — rewrites.json → equiv → smt2 → prove
- `generate_egg.sh` — rewrites.json → equiv → `../../c2po/egglog/rewrites/{temporal,const_folding}.egg`
- `generate_equiv_files.py` / `generate_smt2_equiv.sh` / `prove.sh` / `generate_egglog.py` — pipeline tools
- `generate_latex_table.py` — optional LaTeX table export
- `equiv/`, `smt2/` — generated proof obligations

## Run

Requires `cvc5` and `z3` on `PATH` for the prove step.

```bash
./prove_rewrites.sh [timeout] [jobs]      # defaults: 60s, 8 jobs
./generate_egg.sh                         # write temporal/const_folding.egg
```

Each generated `.smt2` file encodes the *negation* of a rewrite's equivalence,
so `UNSAT` means the rewrite is valid.

## Manual steps

```bash
python3 generate_equiv_files.py rewrites.json equiv/
./generate_smt2_equiv.sh equiv/ smt2/ ../../c2po.py
./prove.sh smt2/
PYTHONPATH=../.. python3 generate_egglog.py \
  equiv/ rewrites.json ../../c2po/egglog/rewrites
```
