# FRET Formalization Template Benchmarks

MLTL benchmarks from FRET's **288 template keys**.

| Tree | Source JSON | Meaning |
|------|-------------|---------|
| `mltl/` | `semantics_no_rewrites.json` | Original formalizations |
| `mltl_with_rewrites/` | `semantics_with_rewrites.json` | Same templates after FRET rewrites |

- Placeholders `$scope_mode$`, `$regular_condition$`, `$post_condition$`,
`$stop_condition$` → `a0`, `a1`, `a2`, `a3` (`.mltl` atomic form; the analysis
scripts use `mode`/`regular`/`post`/`stop` in `.c2po`)
- Duration sugar (`G[<=$duration$]`, `F[<$duration$+1]`, …) uses `duration` **(N)**
- Mission-time bound `M` uses `mission_time`

## Layout

```
fret/
  generate_mltl_files.py
  semantics_no_rewrites.json
  semantics_with_rewrites.json
  mltl/
  mltl_with_rewrites/
    M100_N20/              # M=100,   duration=20
    M1000_N20/             # M=1000,  duration=20
    M10000_N20/            # M=10000, duration=20
      after_holding_after_satisfaction.mltl
      …
```

Filenames are sanitized template keys (e.g. `after,holding,always,satisfaction`
→ `after_holding_always_satisfaction.mltl`). Matching names across the two trees
line up for pairwise comparison.

## Generate

```bash
python3 generate_mltl_files.py
```

Generates **both** `mltl/` and `mltl_with_rewrites/` from the JSON files
in this directory.
