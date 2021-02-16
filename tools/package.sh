#!/bin/bash

# This script will package

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 DIRECTORY README" >&2
  echo -e "DIRECTORY \t top level directory of r2u2 version to package" >&2
  echo -e "README \t\t README file to be placed at top level of package" >&2
  exit 1
fi

echo "Packaging $1 version of r2u2"

DATE=$(date +"%m-%d-%Y")
PACKAGE="${1##*/}_${DATE}"

if [ -d $PACKAGE ]; then
  echo "Package directory already exists, delete $PACKAGE first"
  exit 1
fi

mkdir "$PACKAGE"
mkdir "${PACKAGE}/tools"
mkdir "${PACKAGE}/test"

cp -v -r tools/Assembler tools/Compiler tools/Config "${PACKAGE}/tools"
cp -v -r test/AT test/Inputs test/Oracle test/TL_formula "${PACKAGE}/test"
cp -v -r "${1}/src" "${1}/Makefile" tools/r2u2prep.py $2 $PACKAGE
# copy any additonol files you would like here:
#cp -v tools/split_verdicts.sh "${PACKAGE}/tools"

tar -czvf "${PACKAGE}.tar.gz" $PACKAGE

# remove this if you still want a copy of non-archived package
#rm -rf $PACKAGE
