# EQSat Rewrite Scripts

Files for proving correctness of rewrite rules and generating egglog files for use in equality
saturation.

- `complete.json`/`incomplete.json` contain rewrite rules in a standard format.
- `generate_equiv_files.py` generates .equiv files from rewrites.json.
- `generate_egglog.py` generates egglog files from .equiv files.
- `generate_smt2_equiv.sh` generates SMT2 files from .equiv files.

If you edit `rewrites.json`, generate new .equiv files (in `equiv/`):

    python3 generate_equiv_files.py rewrites.json equiv/

Then generate the corresponding egglog and place it where c2po can find it:

    python3 generate_egglog.py equiv rewrites.json ../../c2po/egglog

Finally, re-generate the SMT2 encoding for the equivalence proofs:

    ./generate_smt2_equiv.sh equiv/ smt2/

The proof obligations can be dispatched via the `compiler/scripts/prove.sh` script for parallel
solving (assuming cvc5 and z3 are installed).
