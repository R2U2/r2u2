#!/usr/bin/env bash
set -o errexit
set -o nounset

infile="${1:-}"
outdir="${2:-}"

if [ ! -f "${infile}" ]; then
  echo "File '${infile}' not found"
else
  if [ ! -d "${outdir}" ]; then
    outdir="."
  fi
  filename=$(basename -- "${infile}")
  awk -F: -v filebase="${filename%.*}" -v outdir="${outdir%.*}" '{print $2 >(outdir "/" filebase ".log." $1)}' "${infile}"
fi