#!/usr/bin/env bash
set -o errexit
set -o nounset

infile="${1:-}"
if [[ ! -f "${infile}" ]]; then
  echo "File '${infile}' not found"
else
  echo "Splitting ${infile} by formula ID"
  filename=$(basename -- "${infile}")
  awk -F: -v filebase="${filename%.*}" '{print $2 >(filebase "_formula" $1 ".txt")}' "${infile}"
fi

