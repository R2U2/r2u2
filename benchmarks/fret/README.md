# FRET Formalization Template Benchmarks

MLTL benchmarks from FRET's **288 formalization templates**.

| Tree | Source JSON | Meaning |
|------|-------------|---------|
| `mltl/` | `semantics_no_rewrites.json` | Original formalizations |
| `mltl_with_rewrites/` | `semantics_with_rewrites.json` | Same templates after FRET rewrites |

Instantiation matches
[`comparison_mltl_mem.py`](../../IntegratingFRETAndR2U2Analysis/Scripts/comparison_mltl_mem.py):

- Placeholders `$scope_mode$`, `$regular_condition$`, `$post_condition$`,
  `$stop_condition$` → `a0`, `a1`, `a2`, `a3` (`.mltl` atomic form; the analysis
  scripts use `mode`/`regular`/`post`/`stop` in `.c2po`)
- Duration sugar (`G[<=$duration$]`, `F[<$duration$+1]`, …) uses **`duration` (N)**
- Mission-time bound `M` uses **`mission_time`**

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

## Regenerate

```bash
python3 generate_mltl_files.py
```

Always regenerates **both** `mltl/` and `mltl_with_rewrites/` from the JSON files
in this directory.

## Benchmark

`benchmark.sh` runs every formula under six modes and writes six JSON files
(864 entries each) under `results/` by default:

| Output | Input tree | Optimization |
|--------|------------|--------------|
| `control_no_rewrites.json` | `mltl/` | none |
| `control_with_rewrites.json` | `mltl_with_rewrites/` | none |
| `ilp_ac.json` | `mltl/` | eqsat ILP + AC |
| `ilp_no_ac.json` | `mltl/` | eqsat ILP |
| `greedy_ac.json` | `mltl/` | eqsat greedy + AC |
| `greedy_no_ac.json` | `mltl/` | eqsat greedy |

The per-file c2po script matches
`benchmarks/scripts/eqsat/benchmark.sh` lines 374–405 (parse → type-check →
desugar → CSE → atomics → optional `optimize_eqsat` → CSE → SCQ → assemble →
stats).

```bash
./benchmark.sh --timeout 5 --memout 4000 --num-jobs 8
./benchmark.sh --timeout 5 --memout 4000 --num-jobs 8 --output-dir ./results
# Smoke test (first n formulas only):
./benchmark.sh --timeout 2 --memout 500 --num-jobs 2 --limit 2 --output-dir /tmp/fret_smoke
# Subset of modes:
./benchmark.sh --timeout 5 --memout 4000 --num-jobs 8 --modes ilp_ac,greedy_ac

# Plots (vs control_no_rewrites; includes control_with_rewrites + eqsat modes):
python3 plot_results.py --results-dir ./results --output-dir ./results/plots
```

## Apptainer

`apptainer/` builds a self-contained image (egglog, Z3, cvc5, Gurobi venv,
c2po, and both formula trees) whose runscript is `benchmark.sh`:

```bash
cd apptainer
./apptainer_build.sh                      # -> fret_benchmark.sif
apptainer run --bind /path/to/gurobi.lic:/root/gurobi.lic fret_benchmark.sif \
    --timeout 3600 --memout 64000 --num-jobs 20 --output-dir "$PWD/results"
```

The image is read-only, so `--output-dir` must point at a writable host path.
ILP modes require a Gurobi license bound to `/root/gurobi.lic`.

For a cluster, `generate_slurm.sh` writes one SLURM job per mode:

```bash
./generate_slurm.sh --benchmark-sif fret_benchmark.sif \
    --output-dir /scratch/fret_results --gurobi-lic ~/gurobi.lic
sbatch fret_ilp_ac.slurm   # etc.
```

## Profiles

| Profile     | Mission time `M` | Duration `N` |
|-------------|-----------------:|-------------:|
| `M100_N20`  | 100              | 20           |
| `M1000_N20` | 1000             | 20           |
| `M10000_N20`| 10000            | 20           |

These `M`/`N` pairs match the subplot figure in
`comparison_mltl_mem_graph.py` (`preprocessed_data_M_{100,1000,10000}_N_20.csv`).
