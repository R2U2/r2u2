some notes:

- transmormer.py is the main application
- inputs and samplerate are defined in inputs.py
- generated files are stored in the working directory, this are
    - logged_data.dat, testbench input data in binary format, each line represents a sample as std_logic_vector
    - logged_data.csv, the same data in decimal
    - log_input_pkg.vhd, package with functions to extract data from the input std_logic_vector
    - at_checkers.vhd, module which instantiates all atCheckers
