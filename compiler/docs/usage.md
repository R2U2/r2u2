# C2PO Usage
C2PO requires a specification file and a file for generating a signal mapping (i.e., to tell which variable each input corresponds to during runtime).

To compile a specification, run the `r2u2prep.py` script with a `.csv` or `.map` file as argument. One of the `--booleanizer` or `--atomic-checker` flags must be set. For instance, to run the `cav` example:

    python r2u2prep.py --booleanizer examples/cav.mltl examples/cav.csv 

The assembled binary should be at `r2u2_spec.bin` by default and is ready to be run by a properly configured R2U2 over input data. For full compiler options:

    python r2u2prep.py -h