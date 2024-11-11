# Testing

Most testing is handled by the top-level integration framework, however unit tests and static analysis are manged per sub-project.

## Unit testing with Munit

Unit testing for the R2U2 static monitor is handled with the [munit](https://nemequ.github.io/munit/) unit testing framework.
The framework itself is vendored under the `external` sub-directory and the test suite is located under `test`.
Every .c file in the `test` directory is automatically detected by the Makefile and linked with the R2U2 debug library as well as the munit framework to produce test harness binaries.

## Unit Testing Coverage Analysis

Test coverage is provided by post-processing the `.gcno` tracing files produced by executing the test harnesses into an HTML report.
First `gcov` is used to convert the tracing format into a per-file report, then `gocvr` is used to generate an aggregate report.

To automate this process the following three shell commands are invoked by the Makefile when running the `check` target:

```bash
run_all_tests = (find ./bin/test -maxdepth 1 -type f -name 'test_*' -exec {} \;)
coverage_proc = (find $(DBG_PATH) -name "*.gcno" -exec gcov -b -l -p -c {} \; && mv *.gcov $(TST_RPT_PATH))
coverage_html = (gcovr -g -k -r $(SRC_PATH) -e '.*_pt\.c' $(TST_RPT_PATH) --html --html-details -o $(TST_RPT_PATH)/index.html)
```

## Static Analysis with CodeChecker

To provide static analysis of the C code, the following tools are ran before being aggregated into a unified report by [CodeChecker](https://codechecker.readthedocs.io/en/latest/):
- [Clang Static Analyzer](https://clang-analyzer.llvm.org/)
- [Clang Tidy](https://clang.llvm.org/extra/clang-tidy/)
- [Cppcheck](https://codechecker.readthedocs.io/docs/tools/report-converter.md#cppcheck)
- [Infer](https://codechecker.readthedocs.io/docs/tools/report-converter.md#facebook-infer)
- [cpplint](https://codechecker.readthedocs.io/docs/tools/report-converter.md#cpplint)

This procedure is used to generate the final report:
```bash
make clean
compiledb --command-style make
compdb list > compile_commands.with_headers.json
mv compile_commands.with_headers.json compile_commands.json

mkdir -p ./reports
mkdir -p ./reports/infer
mkdir -p ./reports/cpplint

infer capture --compilation-database compile_commands.json --results-dir ./reports/infer
infer analyze -q --results-dir ./reports/infer
infer report -q --results-dir ./reports/infer
report-converter -t fbinfer -o ./reports ./reports/infer

cpplint --verbose=0 --counting=detailed --linelength=80 --recursive --includeorder=standardcfirst src > ./cpplint_report.log 2>&1
report-converter -t cpplint -o ./reports ./cpplint_report.log
mv ./cpplint_report.log reports/cpplint/report.log

PATH=$(brew --prefix llvm)/bin:$PATH CodeChecker analyze ./compile_commands.json --output ./reports

CodeChecker parse ./reports
```
