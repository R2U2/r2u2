
# About
The Realizable, Reconfigurable, Unobtrusive Unit (R2U2) is a runtime verification
framework designed to monitor safety- or mission-critical systems with
constrained computational resources. 

## Citing R2U2

If you would like to cite R2U2, please use our 2023 CAV paper: 

*Johannsen, Chris, Jones, Phillip, Kempa, Brian, Rozier, Kristin Yvonne, & Zhang, Pei. (2023). R2U2 V3 Demonstration Artifact for the 35th International Conference on Computer Aided Verification (CAV'23). International Conference on Computer Aided Verification (CAV), Paris, France. Zenodo. https://doi.org/10.5281/zenodo.7889284*

# Running R2U2

To run your own specifications and inputs with R2U2, consult the README files
included in r2u2/ and its sub-directories. As a brief overview:

1) Write a MLTL specification file as described by `compiler/README.md`

2) Write a CSV file with your signal inputs and a header naming them

3) Feed those files to the C2PO formula compiler:
        
        python3 compiler/c2po.py --booleanizer --trace "path/to signals.csv" "path/to/spec.c2po" 

4) Build R2U2 monitor (this only has to be done once, not every time you 
   change the spec):
    
        pushd monitor/ && make clean all && popd

5) Run R2U2:
    
        ./monitor/build/r2u2 "path/to/r2u2_spec.bin" "path/to/input.csv"

5) Examine the output `R2U2.log` file, note that aggregated writes means some
timestamps will appear to be "skipped" - this is normal.

# Requirements 

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

# Example Cases

Each of the following cases shows a minimal example of a feature discussed in
the paper in the indicated section:
- `agc`         Assume-Guarantee Contract: tri-state status 
                              output (inactive, invalid, or verified)
- `arb_dataflow`    Arbitrary Data-Flow: Feeding a temporal engine 
                            results back to the atomic checker
- `atomic_checker`  Atomic Checker: various signal processing examples
- `cav`             CAV: The example from the paper showcasing a 
                              realistic composition of the other features
- `cse`             Common Subexpression Elimination: Removal of 
                              redundant work from specification
- `set_agg`          Set Aggregation: Specifications beyond binary 
                              inputs
- `sets`            Set Types: Use of parametrized typing on a 
                              structure member
- `simple`          Simple: A basic R2U2 V2 style specification in the 
                            V3 input language
- `struct`          Structure: Use of a structure to group variables

Beyond these examples tailored to this paper, further examples can be found in
the test subdirectories: `r2u2/test` and `r2u2/compiler/test`

# Running the GUI

Run the `GUI/run.py` script to start the web server then open a web browser and navigate to
http://127.0.0.1:8050/.

# Support 

If you believe you have found a case of unsound output from R2U2,
please run the case in debug mode and provide the output to the authors for
analysis: 
    `pushd r2u2/monitor && make clean debug && popd`
    `./r2u2/monitor/build/r2u2_debug "path/to/r2u2_spec.bin" \
        "path/to/input.csv" 2>debug.log` 

The logs contain no identifying information, please ask the chairs to assist in
passing along you anonymized feedback. Thank you.