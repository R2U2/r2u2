import os

template = """#!/bin/bash

# Copy/paste this job script into a text file and submit with the command:
#    sbatch thefilename
# job standard output will go to the file slurm-%j.out (where %j is the job ID)

#SBATCH --time=36:00:00   # walltime limit (HH:MM:SS)
#SBATCH --nodes=1   # number of nodes
#SBATCH --ntasks-per-node=20   # 20 processor core(s) per node 
#SBATCH --mem=384G   # maximum memory per node
#SBATCH --mail-user=cgjohann@iastate.edu   # email address
#SBATCH --mail-type=END
#SBATCH --job-name="{}"   # Job name to display in squeue
#SBATCH --output="{}"   # Job standard output file

# LOAD MODULES, INSERT CODE, AND RUN YOUR PROGRAMS HERE
module load apptainer
cd /work/kyrozier/cgjohann/mltlsat
apptainer run container.sif random/{} {} {} results/{} --smt-max-time 1200 --smt-max-memory 16000 {}
"""

benchmarks = [
    "random-4",
    "random-8",
    "random-16",
    "random-32",
    "random-64",
    "random-128",
    "random-256",
    "random-512",
    "random-1024",
    "random-2048",
    "random-4096",
    "random-8192",
]

configurations = [
    {
        "solver": "z3",
        "encoding": "uflia",
    },
    {
        "solver": "z3",
        "encoding": "auflia",
    },
    {
        "solver": "z3",
        "encoding": "qf_auflia",
    },
    {
        "solver": "z3",
        "encoding": "aufbv",
    },
    {
        "solver": "z3",
        "encoding": "qf_aufbv",
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
        "encoding": "auflia",
        "options": ["--fmf-bound", "--finite-model-find", "--arrays-exp"],
    },
    {
        "solver": "cvc5",
        "encoding": "qf_auflia",
        "options": ["--fmf-bound", "--finite-model-find", "--arrays-exp"],
    },
    {"solver": "cvc5", "encoding": "aufbv", "options": ["--arrays-exp"]},
    {"solver": "cvc5", "encoding": "qf_aufbv", "options": ["--arrays-exp"]},
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
        "solver": "yices-smt2",
        "encoding": "qf_auflia",
    },
    {
        "solver": "yices-smt2",
        "encoding": "qf_aufbv",
    },
    {
        "solver": "yices-smt2",
        "encoding": "qf_bv",
    },
    {
        "solver": "yices-smt2",
        "encoding": "qf_bv_incr",
    },
]

os.makedirs("slurm", exist_ok=True)

for config in configurations:
    for benchmark in benchmarks:
        if config["encoding"] == "qf_bv_incr" and benchmark in {
            "random-4",
            "random-8",
            "random-16",
            "random-32",
            "random-64",
            "random-128",
            "random-256",
        }:
            continue

        experiment_name = f"{config['solver']}.{config['encoding']}.{benchmark}"
        with open(f"slurm/{experiment_name}.slurm", "w") as f:
            content = template.format(
                benchmark,
                f"{benchmark}.out",
                benchmark,
                config["solver"],
                config["encoding"],
                f"{experiment_name}.csv",
                " ".join(
                    [f'--solver-option="{opt}"' for opt in config.get("options", [])]
                ),
            )
            f.write(content)
