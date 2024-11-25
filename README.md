
# About

The Realizable, Reconfigurable, Unobtrusive Unit (R2U2) is a runtime verification framework designed
to monitor safety- or mission-critical systems with constrained computational resources. 

## Citing R2U2

If you would like to cite R2U2, please use our 2023 CAV paper: 

*Johannsen, Chris, Jones, Phillip, Kempa, Brian, Rozier, Kristin Yvonne, & Zhang, Pei. (2023). R2U2 V3 Demonstration Artifact for the 35th International Conference on Computer Aided Verification (CAV'23). International Conference on Computer Aided Verification (CAV), Paris, France. Zenodo. https://doi.org/10.5281/zenodo.7889284*

# Running R2U2

To run R2U2 over a simulated trace:

1) Write a specification file as described by `compiler/README.md` (or using an example from
   `examples/`).

2) Write a CSV file with your signal inputs and a header naming them.

3) Feed those files to the C2PO formula compiler:
        
        python3 compiler/c2po.py --trace path/to/trace.csv path/to/spec.c2po 

4) Build R2U2 monitor (this only has to be done once, not every time you 
   change the spec):
    
        cd monitors/c && make clean all && cd ../../

5) Run R2U2:
    
        ./monitors/c/build/r2u2 path/to/spec.bin path/to/trace.csv

See `examples/run_examples.sh` for example uses.

# Requirements 

The following dependencies are required to run R2U2 and C2PO: 
- Make 
- C99 compiler 
- Python 3.6 or greater

# Example Cases

Examples can be found in the examples and test subdirectories: `examples/`, `test/`, and
`compiler/test`.

# Support 

If you believe you have found a case of unsound output from R2U2, please run the case in debug mode
and open an issue with the output for analysis: 

    cd monitors/c && make clean debug && cd ../../
    ./monitors/c/build/r2u2_debug path/to/spec.bin path/to/trace.csv 2> debug.log

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the
work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
