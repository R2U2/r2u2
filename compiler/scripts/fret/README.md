# FRET Rewrite Pipeline

Scripts for normalizing, grounding, proving, and packaging FRET paper rewrite
rules for use in C2PO equality saturation.

## Files

- `normalize_fret_rewrites.py` — FRET paper rules → `fret_rewrites.json`
- `ground_rewrites.py` — ground compound interval bounds in `pre` terms →
  `fret_rewrites_grounded.json`
- `prepare.sh` — shared dependency: normalize → ground → `equiv/`
- `prove_rewrites.sh` — prepare → smt2 → prove
- `generate_egg.sh` — prepare → `../../c2po/egglog/rewrites/fret.egg`
- `equiv/`, `smt2/` — generated proof obligations

Shared generators live in the parent `scripts/` directory
(`generate_equiv_files.py`, `generate_smt2_equiv.sh`, `prove.sh`,
`generate_egglog.py`).

## Run

Requires `cvc5` and `z3` on `PATH` for the prove step.

```bash
./prepare.sh                              # refresh JSON + equiv/
./prove_rewrites.sh [timeout] [jobs]      # defaults: 60s, 8 jobs
./generate_egg.sh                         # write fret.egg
```

`prove_rewrites.sh` and `generate_egg.sh` each call `prepare.sh` first, so either
can be run alone after editing the FRET rules.

## Manual steps

```bash
python3 normalize_fret_rewrites.py
python3 ground_rewrites.py fret_rewrites.json fret_rewrites_grounded.json
python3 ../generate_equiv_files.py fret_rewrites_grounded.json equiv/
../generate_smt2_equiv.sh equiv/ smt2/ ../../c2po.py
../prove.sh smt2/
PYTHONPATH=../.. python3 ../generate_egglog.py \
  equiv/ fret_rewrites_grounded.json ../../c2po/egglog/rewrites --bundle fret.egg
```
