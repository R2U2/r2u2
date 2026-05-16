# Artifact for "Shrinking Mission-time LTL Runtime Monitors with Equality Saturation", FMCAD 2026

This is the artifact for the paper "Shrinking Mission-time LTL Runtime Monitors with Equality
Saturation" submitted to FMCAD 2026. The paper implements a toolchain for optimizing Mission-time
LTL (MLTL) formulas for lower resource usage via Equality Saturation (EqSat). The toolchain extracts
an optimized formula from the output of EqSat using either an external ILP solver or a greedy
algorithm (embedded into the EqSat encoding). EqSat uses a set of rewrites to explore the space of
derivable formulas. To prove the selected rewrites equivalent, the toolchain uses an SMT-based
equivalence checking technique. R2U2 uses a data structure called an SCQ internally, so all
references to SCQs are the same as MemDAG as in the paper.

The toolchain implements the optimization in the Configuration Compiler for Property Organization
(C2PO), the formula compiler for the runtime verification framework R2U2. It uses EggLog for
equality saturation, Gurobi for ILP solving, and Z3 and CVC5 for SMT solving.

The paper ran the experiments on the Nova HPC cluster at Iowa State University. Each node used AMD
EPYC 9655 processors with a minimum of 64 cores and 1.5TB per node running RHEL 9.6. Each benchmark
ran with exclusive access to a node and a maximum time of 1 hour (separately for Gurobi and EggLog)
and memory of 64GB. 

## Running the Docker Image

The artifact image is distributed as a tarball `mltleqsat.tar`. Load it into your local
Docker daemon, then start an interactive shell. The image expects a Gurobi license at
`/root/gurobi.lic` inside the container (`GRB_LICENSE_FILE` is set in the Dockerfile), so mount
your host license file there. Mount a host directory onto `/opt/benchmarks/results` so the
JSON results and any plots written under that path appear on your machine without copying them out of the
container.

```bash
docker load -i mltleqsat.tar
docker run -it --rm \
  -v /path/to/your/gurobi.lic:/root/gurobi.lic \
  -v /path/to/your/results:/opt/benchmarks/results \
  mltleqsat bash
```

After `docker load`, use the image name and tag printed by Docker (often `mltleqsat:latest`) in
place of `mltleqsat` if yours differs. Remove the `--rm` flag for the docker state to remain
consistent across multiple runs of the container.

## Apptainer

We also provide the Apptainer image that was run on the Nova cluster for convenience and
completeness (`apptainer/benchmark.sif`) and some utilities for using it. First, to generate a
`benchmarks.txt` file, run

```bash
./get_benchmarks.sh /path/to/benchmarks/
```

There is a `generate_slurm.sh` script for generating the five slurm files, which can be run via:

```bash
./generate_slurm_benchmarks_txt.sh \
  --benchmark-sif /path/to/benchmark.sif \
  --input-file-list /path/to/benchmarks.txt \
  --output-dir /path/to/output
```

This option requires a non-named-user (i.e., institutional) Gurobi license to run the ILP extraction
methods (see Dependencies below).

## Structure

```
/opt
├── benchmarks/             # Benchmarks, generated benchmark list, run scripts, analysis scripts, and results.
│   ├── boeing-wbs/         # Boeing WBS benchmark inputs (.c2po).
│   ├── nasa-atc/           # NASA ATC benchmark inputs (.c2po).
│   ├── mtl-patterns/       # MTL pattern benchmark inputs (.mltl).
│   ├── mavlink/            # MAVLink benchmark inputs (.mltl/.c2po).
│   ├── fluxgate/           # Fluxgate benchmark inputs (.mltl/.c2po).
│   ├── utm/                # UTM benchmark inputs (.mltl/.c2po).
│   ├── scripts/            # Executable benchmark driver scripts.
│   ├── analysis/           # Plotting/report helpers for benchmark post-processing.
│   ├── paper-results/      # Frozen result artifacts used in the paper.
│   └── results/            # Output directory for newly generated benchmark runs.
├── compiler/               # c2po compiler source tree and supporting scripts.
├── rewrites/               # Rewrite-rule tooling.
├── z3/                     # Bundled Z3 solver installation.
├── cvc5/                   # Bundled cvc5 solver installation.
├── egglog/                 # Built egglog checkout (v2.0.0).
├── egglog-experimental/    # Built egglog-experimental checkout (pinned commit).
└── venv/                   # Python virtual environment (includes gurobipy).
```

## Dependencies

- Base image: `ubuntu:24.04`
- Python: system `python3` from Ubuntu 24.04 + virtual environment at `/opt/venv`
- Rust toolchain: installed via `rustup` (not pinned in `Dockerfile`)
- Z3: `4.15.0` (`z3-4.15.0-x64-glibc-2.39`)
- cvc5: `1.3.3`
- egglog: `v2.0.0`
- egglog-experimental: commit `38b3898`
- gurobipy: `12.0.3` (requires a license, a free academic license can be obtained at
  https://www.gurobi.com/academics)

If Gurobi cannot be obtained, then only the greedy methods can be run and analyzed.

Also installed from Ubuntu repositories (version follows Ubuntu 24.04 package set): `git`, `curl`,
`wget`, `unzip`, `build-essential`, `ca-certificates`, `parallel`, `locales`, `patch`, and `vim`.

### Note on egglog-experimental Version

`egglog-experimental` is a fork of `egglog` (supported by the same developers) with an extension
that allows non-constant costs. This is necessary, as costs are assigned based on syntactic
properties of the formula. For consistency, we ensure that `egglog-experimental` is built off of the
locally-built version of `egglog` on the image (see /opt/egglog-experimental/egglog_experimental.patch).

## Smoke Test 

Run inside the Docker image:

```bash
    cd /opt/benchmarks/scripts
    ./smoke_test.sh
```

The script writes four JSON outputs to `benchmarks/scripts/eqsat/smoke-test-results/`:
`greedy_ac.json`, `greedy_no_ac.json`, `ilp_ac.json`, and `ilp_no_ac.json`. For the AC runs,
/opt/benchmarks/mavlink/mltl/dangerous_mavlink.M65535.mltl should timeout.

## Running the Benchmarks

To run the full set of benchmarks:

```bash
    cd /opt/benchmarks/scripts
    ./run_control.sh TIMEOUT MEMOUT NUMJOBS NUM_GUROBI_THREADS /opt/benchmarks/benchmarks.txt
    ./run_greedy_no_ac.sh TIMEOUT MEMOUT NUMJOBS NUM_GUROBI_THREADS /opt/benchmarks/benchmarks.txt
    ./run_greedy_ac.sh TIMEOUT MEMOUT NUMJOBS NUM_GUROBI_THREADS /opt/benchmarks/benchmarks.txt
    ./run_ilp_no_ac.sh TIMEOUT MEMOUT NUMJOBS NUM_GUROBI_THREADS /opt/benchmarks/benchmarks.txt
    ./run_ilp_ac.sh TIMEOUT MEMOUT NUMJOBS NUM_GUROBI_THREADS /opt/benchmarks/benchmarks.txt
```

The experiments reported in the paper used `TIMEOUT=3600` (in seconds), `MEMOUT=64000` (in MB),
`NUMJOBS=20`, and `NUM_GUROBI_THREADS=0`. A 0 value for any argument means no limit. The time taken
to run each script on the Nova cluster with limits as described:

- control: ~1min
- greedy_no_ac: ~1min 
- greedy_ac: ~45min
- ilp_no_ac: ~4hrs
- ilp_ac: ~20hrs

**When running parallel jobs it is important to note any limits on concurrent sessions for Gurobi (example: WLS academic license only allows 2 sessions to be run at once).**
**If more than this number of jobs are run the ILP scripts may sporadically fail if more than 2 instances are solving ILP problems at one time.**

We also provide a random subset of 200 benchmarks in `/opt/benchmarks/subset.txt`. To run these, use
the path to `subset.txt`, for example:

```bash
    ./run_greedy_no_ac.sh TIMEOUT MEMOUT NUMJOBS NUM_GUROBI_THREADS /opt/benchmarks/subset.txt
```

The time taken using `TIMEOUT=600`, `MEMOUT=16000`, `NUMJOBS=2`, and `NUM_GUROBI_THREADS=8` (which
provides a reasonable reflection of the paper results) on a machine with a 32-core AMD Ryzen 9 9950X
and 64GB RAM:

- control: ~1min
- greedy_no_ac: ~1min 
- greedy_ac: ~7min
- ilp_no_ac: ~45mins
- ilp_ac: 3hrs

The `/opt/benchmarks/analysis` directory has a number of scripts for analyzing the data and
generating the tables/figures as in the paper. To generate the plots and tables, run:

```bash
    cd /opt/benchmarks/analysis
    ./generate_plots.sh
    ./generate_tables.sh
```

There are also scripts for generating the plots and table from the paper results:

```bash
    ./generate_plots_paper.sh
    ./generate_tables_paper.sh
```

## Interpreting the results file

Each benchmark driver writes a single JSON object with a top-level `"results"` array. Every element
is one benchmark instance: an absolute path in `"filename"` (from the machine that ran the job, for
example under `/work/...` in the frozen paper copies under
`benchmarks/scripts/eqsat/paper-results/`) plus exactly one nested object of statistics.

Across files, rows that refer to the same benchmark share the same `"filename"` string; downstream
scripts (for example `benchmarks/scripts/eqsat/analysis/plot_results.py`) align rows by that field.
The order of entries inside `"results"` need not match between files.

Fields inside the nested object include:

- `formula`: MLTL formula string after the run’s pipeline (control rows skip EqSat; optimized rows contain the extracted formula).
- `scq`: Total SCQ size, the same as MemDAG in the paper.
- `dag-size`: size of the formula DAG.
- `num-temporal-operators`: count of temporal operators in the formula.
- `egglog-status`, `egglog-encoding-time`, `egglog-solver-time`: EggLog equality-saturation phase outcome and timings (seconds). 
- `num-eclasses`, `num-enodes`: e-graph shape after EqSat (control runs typically report `0` because EqSat is not invoked).
- `gurobi-status`, `gurobi-encoding-time`, `gurobi-solving-time`: Gurobi ILP extraction phase when used; status strings mirror the compiler (for example `"ok"`, or substrings such as `"timeout"` / `"memout"` for resource limits; encoding failures may be reported on the encoding step—see `benchmarks/scripts/eqsat/analysis/report_results.py` for how counts are bucketed).
- `num-tl-temporal-instructions`, `num-tl-instructions`: counts from the R2U2 assembly after `assemble` (and related steps).
- `sabre-total-bytes`: size in bytes of the generated SABRe monitor code (`generate_sabre_code`).

## Proving the Rewrites Correct

We provide a utility script that generates a set of SMTLIB2 files for each rewrite such that if the
SMTLIB2 is unsatisfiable, then the the two formulas in the rewrite are equivalent. The script also
generates the EggLog encoding from the rewrites automatically. The rewrites can be found in
`opt/rewrites/rewrites.json`.

```bash
    cd /opt/rewrites
    ./generate_egglog_and_prove.sh TIMEOUT NUM_CVC5_JOBS
```

Running with `TIMEOUT=600` and `NUM_CVC5_JOBS=24`, 7 formulas were unproven (either `UNKNOWN` or
`TIMEOUT`) and took ~1hr10min on the 32-core AMD machine described above. None should return `SAT`
(which implies the two formulas in a rewrite are *not* equivalent).

## Notes

### Runtime Reproducibility

The runtime may differ significantly between runs for some instances due to the behavior of Gurobi.
It appears likely this is due to variable ordering sensitivity in the solver. Since EggLog does not
promise consistent naming and ordering across runs, and this output determines the input to Gurobi,
we cannot promise consistent runtimes for Gurobi. It is expected, therefore, that some instances
timeout on some runs but not others, and vice versa. But, generally, we find the results and
high-level takeaways remain robust across runs.

### Gurobi-specific Notes

### Inconsistent Behavior

There are two instances found while testing that Gurobi rarely reported as having "infeasible"
constraints:

- benchmarks/nasa-atc/10_100/acdr_predicted_far_norm_guarantee.c2po
- benchmarks/nasa-atc/100_1000/acdr_predicted_far_norm_guarantee.c2po

After investigating the encoded ILP models, we could not find any difference between them on runs
where Gurobi returned "infeasible" and "feasible". All models had the exact same number of
constraints of the same type and number of variables of the same type, with the only difference
appearing to be variable naming. 

### Max Memory

Gurobi uses memory in two ways: while building the model and while optimizing the model. The memory
limit set for Gurobi only checks the limit during the optimization, not while building the model.
For some instances (less than 10), building the model uses GBs of memory (sometimes over 8GB), so
the overall process uses the amount of memory used for building the model *plus* the set max memory
for Gurobi. This does not appear to affect the overall takeaways of the data, but is important for
considering how much memory you might use given your specific machine specs.

### Possible Errors

Occasionally Gurobi will be killed by either a SIGKILL or SIGBUS signal. We suspect this is due to
issues with multiprocessing with the WLS license. We did not see these issues with the institutional
license on the Nova cluster. These errors will look like: 

```
environment: line 1: 50881 Bus error               python3 "$(basename "$c2po_path")" -s "$temp_template" 2> "$stderr_file"
ERROR,/opt/benchmarks/boeing-wbs/c2po/0_100/properties_3/wbs_arch2bis_inst_never_loss_of_all_wheel_braking_norm_guarantee.c2po,Processing failed
```
or 
```
environment: line 1: 43329 Segmentation fault      python3 "$(basename "$c2po_path")" -s "$temp_template" 2> "$stderr_file"
ERROR,/opt/benchmarks/boeing-wbs/c2po/10_100/properties_1/wbs_arch1_inst_never_loss_of_all_wheel_braking_norm_guarantee.c2po,Processing failed
```

If this occurs, *either* run the benchmark script again with `NUMJOBS=1` or do the following:

1. Create a new benchmark file with just the file path(s) that failed (named, say, `failures.txt`)
2. Run the following:

```bash
"opt/benchmark/scripts/benchmark.sh" \
  --input-file-list "/opt/benchmarks/failures.txt" \
  --output-json "/opt/benchmarks/results/failures.json" \
  --multi-arity \
  --timeout TIMEOUT \
  --memout MEMOUT \
  --num-jobs NUMJOBS \
  --num-gurobi-threads NUM_GUROBI_THREADS
  --extraction-method ilp \
  --[no-]assoc-comm \
```

3. Insert the resulting JSON object(s) into the respective results JSON. If that file created an
   error message in the original JSON, remove it.
