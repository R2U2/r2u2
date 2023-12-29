# Web MLTL Compiler
Web app for C2PO/R2U2 resource estimation and visualization. To run the GUI:

1. Change directory to `GUI` using `cd r2u2/GUI` 
1. Install requirements via `pip install -r requirements.txt`
2. Run the GUI using `python3 run.py`

## GUI Description

### C2PO 
The GUI provides an input box to enter a specification in C2PO input file format and compile the specification using C2PO. There are some controls for options for the compilation here, including which front-end to enable and whether to enable CSE. To compile, use the blue "Compile" button. If there are any errors or warnings in the input file, they will appear in the "C2PO Log" box. The generated assembly is printed to the right-hand side of the GUI in the "Assembly" box.

### Hardware/Software Configuration
These sections of the GUI estimate the required time and memory to compute the answer to a given specification in the worst-case. For software, one can configure the clock frequency as well as the estimated latency for each operation. For hardware, one can configure in much more fine-grain detail, including LUT type, timestamp width, and more. The hardware estimation values are the only values that impact the graph depicting resource requirements (either number of LUTs or BRAM size).

<!-- Details on how these estimations are computed can be found at {footcite:p}`JJKRZ23`. -->

### AST Visualization
Finally, there is a box for visualizing the AST for the input specification. This is especially useful for seeing how a specification may be re-written to require less resources, since memory requirements are dependent on properties of sibling nodes in the AST. Hovering over a node in the AST will display its corresponding data in the box in the upper right. 

