#!/bin/bash

# Copy/paste this job script into a text file and submit with the command:
#    sbatch thefilename
# job standard output will go to the file slurm-%j.out (where %j is the job ID)

#SBATCH --time=36:00:00   # walltime limit (HH:MM:SS)
#SBATCH --nodes=1   # number of nodes
#SBATCH --ntasks-per-node=36   # 36 processor core(s) per node 
#SBATCH --mem=369G   # maximum memory per node
#SBATCH --mail-user=cgjohann@iastate.edu   # email address
#SBATCH --mail-type=END

# LOAD MODULES, INSERT CODE, AND RUN YOUR PROGRAMS HERE
module load apptainer

cd /work/kyrozier/cgjohann

apptainer run container.sif benchmarks/random/random1 workdir_2 random.csv