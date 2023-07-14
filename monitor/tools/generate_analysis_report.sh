#!/usr/bin/env bash
# generate_analysis_report.sh

# TODO: Move intermediate products to build
# TODO: Check for tool intsalls
# TODO: Linux vs Mac switches

rm -rf reports compile_commands.json
make clean
compiledb --command-style make
compdb list > compile_commands.with_headers.json
mv compile_commands.json compile_commands.no_headers.json
mv compile_commands.with_headers.json compile_commands.json

mkdir -p ./reports
mkdir -p ./reports/infer

infer capture --compilation-database compile_commands.json --results-dir ./reports/infer
infer analyze -q --results-dir ./reports/infer
infer report -q --results-dir ./reports/infer
report-converter -t fbinfer -o ./reports ./reports/infer

cpplint --verbose=0 --counting=detailed \
--filter=-whitespace/line_length,-legal,-build/header_guard,-build/include_subdir \
--includeorder=standardcfirst \
--root=monitor/src --recursive src > ./cpplint_report.log 2>&1
report-converter -t cpplint -o ./reports ./cpplint_report.log
rm ./cpplint_report.log

PATH=$(brew --prefix llvm)/bin:$PATH CodeChecker analyze compile_commands.no_headers.json --output ./reports

CodeChecker parse ./reports
