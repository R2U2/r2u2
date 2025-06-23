import os

NPROCS = 28

template = """#!/bin/bash

#SBATCH --time=120:00:00   # walltime limit (HH:MM:SS)
#SBATCH --nodes=1   # number of nodes
#SBATCH --ntasks-per-node={}   # 28 processor core(s) per node 
#SBATCH --mem=485G   # maximum memory per node
#SBATCH --mail-user=cgjohann@iastate.edu   # email address
#SBATCH --mail-type=END
#SBATCH --job-name="{}"   # Job name to display in squeue
#SBATCH --output="{}"   # Job standard output file
#SBATCH --error="{}"   # Job standard output file
#SBATCH --constraint=epyc-7502

# LOAD MODULES, INSERT CODE, AND RUN YOUR PROGRAMS HERE
module load apptainer
cd /work/kyrozier/cgjohann/mltlsat
apptainer run container.sif {} {} {} {} {}
"""

benchmarks = [
    "random-10",
    "random-100",
    "random-1000",
    "random-10000",
    # "boeing-wbs-1000",
    # "boeing-wbs-10000",
    # "boeing-wbs-100000",
    # "nasa-atc-1000",
    # "nasa-atc-10000",
    # "nasa-atc-100000",
]

configurations = [
    {
        "solver": "z3",
        "encoding": "uflia",
    },
    {
        "solver": "z3",
        "encoding": "qf_bv",
    },
    {
        "solver": "z3",
        "encoding": "qf_bv_incr",
    },
    {
        "solver": "cvc5",
        "encoding": "uflia",
        "options": ["--fmf-bound", "--finite-model-find"],
    },
    {
        "solver": "cvc5",
        "encoding": "qf_bv",
    },
    {
        "solver": "cvc5",
        "encoding": "qf_bv_incr",
    },
    {
        "solver": "bitwuzla",
        "encoding": "qf_bv",
    },
    {
        "solver": "bitwuzla",
        "encoding": "qf_bv_incr",
    },
    {
        "solver": "yices",
        "encoding": "qf_bv",
    },
    {
        "solver": "yices",
        "encoding": "qf_bv_incr",
    },
]

os.makedirs("slurm", exist_ok=True)

for config in configurations:
    for benchmark in benchmarks:
        if (
            (config["encoding"] == "qf_bv_incr"
            or config["encoding"] == "qf_bv_incr")
            and (benchmark == "random-10" or benchmark == "random-100")
        ):
            continue

        experiment_name = f"{config['solver']}.{config['encoding']}.{benchmark}"
        with open(f"slurm/{experiment_name}.slurm", "w") as f:
            content = template.format(
                NPROCS,
                experiment_name,
                f"{experiment_name}.out",
                f"{experiment_name}.err",
                benchmark + ".txt",
                NPROCS,
                config["encoding"],
                config["solver"],
                " ".join(
                    [f'--smt-option="{opt}"' for opt in config.get("options", [])]
                ) if "options" in config else "",
            )
            f.write(content)
