# Compiler Scripts

Shared tooling and rewrite-proof pipelines for C2PO.

## Shared rewrite tooling

Used by both `fret/` and `rewrites/`:

- `generate_equiv_files.py` — JSON rewrite rules → `.equiv` files
- `generate_smt2_equiv.sh` — `.equiv` files → SMT2 encodings via `c2po.py`
- `prove.sh` — parallel cvc5/z3 proofs over an `smt2/` directory (`UNSAT` = proven)
- `generate_egglog.py` — `.equiv` files → egglog rewrite files  
  Use `--bundle FILE` to emit a single combined `.egg` (e.g. `fret.egg`)

## Pipelines

Each of `fret/` and `rewrites/` exposes:

| Script | Purpose |
|--------|---------|
| `./prepare.sh` | Shared dependency: refresh JSON (FRET) and `equiv/` |
| `./prove_rewrites.sh [timeout] [jobs]` | prepare → smt2 → prove |
| `./generate_egg.sh` | prepare → write eggs under `../c2po/egglog/rewrites/` |

| Directory | Source of rules |
|-----------|-----------------|
| [`rewrites/`](rewrites/) | `rewrites.json` |
| [`fret/`](fret/) | FRET paper rules via normalize/ground |

## Other scripts

- `generate_commands_doc.py` — Markdown docs for C2PO commands
- `setup_egglog.sh` / `setup_egglog_experimental.sh` — build egglog (see `egglog*.patch`)
