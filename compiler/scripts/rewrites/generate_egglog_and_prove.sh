#!/bin/bash

set -euo pipefail

usage() {
    echo "Usage: $0 <timeout_seconds> <num_jobs>" >&2
    exit 1
}

if [ "$#" -ne 2 ]; then
    usage
fi

TIMEOUT_SECONDS="$1"
NUM_JOBS="$2"

python3 generate_equiv_files.py rewrites.json equiv/
python3 generate_egglog.py equiv/ rewrites.json /opt/compiler/c2po/egglog/
./generate_smt2_equiv.sh equiv/ smt2/ /opt/compiler/c2po.py
./prove.sh smt2/ "$TIMEOUT_SECONDS" "$NUM_JOBS"
