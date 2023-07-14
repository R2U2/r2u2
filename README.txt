CAV'23 Submission #500 R2U2 Version 3.0: Re-imagining a Toolchain for
Specification, Resource Estimation, and Optimized Observer Generation for
Runtime Verification in Hardware and Software 

Chris Johannsen, Phillip Jones, Brian Kempa, Kristin Yvonne Rozier, Pei Zhang

--------------------------------------------------------------------------------
Summary

The Realizable, Reconfigurable, Unobtrusive Unit is a runtime verification
framework designed to monitor safety- or mission-critical systems with
constrained computational resources. In our paper and this artifact we showcase
the latest features of the flight-certifiable C99 implementation of the runtime
monitor along with its associated formula compiler and resource estimation GUI.
The artifact linked below contains a docker image configured to run R2U2 V3
along with a set of example specifications to demonstrate the advancements noted
in the paper. Additionally, the image can host the resource estimation web GUI
showcased in section 3 for local access. We provide a suite of example
specifications that cover the features highlighted in the paper, along with our
results for comparison. We have archived our tool as a docker container to
ensure consistent behavior across platforms by including all external libraries
and dependencies. R2U2 is very light weight, and expected to perform well on
modest consumer hardware even with the containerization overhead.

--------------------------------------------------------------------------------
Requirements 

The following dependencies have already been installed on this
container for use by the artifact: 
    - Make 
    - C99 compiler 
    - python 3.6 or greater

The following python packages have also been installed via `pip` for testing and
the GUI: 
    - dash 
    - dash-cytoscape 
    - dash-bootstrap-components 
    - pytest 
    - numpy 
    - matplotlib

--------------------------------------------------------------------------------
Organization

|- Home directory
|   |
|   |- logs/            Expected output of included examples
|   |
|   |- r2u2/            R2U2 Source (condensed from the open source version)
|   |   |
|   |   |- compiler/    The C2PO formula compiler
|   |   |
|   |   |- examples/    Inputs and specifications to demo new features
|   |   |
|   |   |- GUI/         Resource Estimation GUI source
|   |   |
|   |   |- monitor/     R2U2 monitor source code
|   |   |
|   |   |- test/        end-to-end testing of C2PO and R2U2
|   |   |
|   |   |- tools/       Used by test-suite to manage R2U2 file types
|   |
|   |
|   |- README.txt       Artifact replication and evaluation instructions
|   |
|   |- run_examples.sh  Runs all included cases and compare with archived logs

--------------------------------------------------------------------------------
Replication instructions 

The included `run_examples.sh` script is
intentionally minimalist to make inspection and replication simple, it will:
    - Build the R2U2 runtime monitor
    - Test the C2PO compiler
    - Run integration tests on C2PO and R2U2 end-to-end
    - Run all the included examples demonstrating the features in the paper
    - Compare the output of the examples to the archived expected results

The program `diff` is run automatically after each case, if there is no output
after the "aliases" definitions produced by the formula compiler before the next
case, the result matched the expected output.

--------------------------------------------------------------------------------
Example Cases

Each of the following cases shows a minimal example of a feature discussed in
the paper in the indicated section:
    - `agc`             [2.2] Assume-Guarantee Contract: tri-state status 
                              output (inactive, invalid, or verified)
    - `arb_dataflow`    [4] Arbitrary Data-Flow: Feeding a temporal engine 
                            results back to the atomic checker
    - `atomic_checker`  [4] Atomic Checker: various signal processing examples
    - `cav`             [2.1] CAV: The example from the paper showcasing a 
                              realistic composition of the other features
    - 'cse'             [2.4] Common Subexpression Elimination: Removal of 
                              redundant work from specification
    - `set_agg`         [2.3] Set Aggregation: Specifications beyond binary 
                              inputs
    - `sets`            [2.1] Set Types: Use of parametrized typing on a 
                              structure member
    - `simple`          [4] Simple: A basic R2U2 V2 style specification in the 
                            V3 input language
    - `struct`          [2.1] Structure: Use of a structure to group variables

Beyond these examples tailored to this paper, further examples can be found in
the test subdirectories: `r2u2/test` and `r2u2/compiler/test`

--------------------------------------------------------------------------------
Exploring CSE 

The `cse` example is run twice, once with common subexpression elimination
disabled, and again with it re-enabled. Both outputs are compared to the same
expected results showing no change in monitor behavior, but the number of
instructions produced by the compiler are different, as seen via the outputted
R2U2 assembly. CSE is enabled by default in C2PO but the flag `--disable-cse`
can be added to turn it off.

--------------------------------------------------------------------------------
Running the GUI

From `r2u2/GUI` run `python run.py` and then open a web browser on either the
host machine or the container (the port is forwarded) and navigate to
[http://127.0.0.1:8050/]

--------------------------------------------------------------------------------
Running R2U2

To run your own specifications and inputs with R2U2, consult the README files
included in r2u2/ and its sub-directories. As a brief overview:
1) Write a MLTL specification file as described by `r2u2/compiler/README.md`
2) Write a CSV file with your signal inputs and a header naming them
3) Feed those files to the C2PO formula compiler:
    `python3 r2u2/compiler/r2u2prep.py --booleanizer "path/to/spec.mltl" \
        "path/to signals.csv"`
4) Build R2U2 monitor (this only has to be done once, not every time you 
   change the spec):
    `pushd r2u2/monitor && make clean all && popd`
5) Run R2U2:
    `./r2u2/monitor/build/r2u2 "path/to/r2u2_spec.bin" "path/to/input.csv"`
5) Examine the output `R2U2.log` file, note that aggregated writes means some
timestamps will appear to be "skipped" - this is normal.

--------------------------------------------------------------------------------
Support 

If you believe you have found a case of unsound output from R2U2,
please run the case in debug mode and provide the output to the authors for
analysis: 
    `pushd r2u2/monitor && make clean debug && popd`
    `./r2u2/monitor/build/r2u2_debug "path/to/r2u2_spec.bin" \
        "path/to/input.csv" 2>debug.log` 

The logs contain no identifying information, please ask the chairs to assist in
passing along you anonymized feedback. Thank you.
