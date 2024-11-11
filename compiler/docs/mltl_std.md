# MLTL Standard Format

C2PO also accepts the MLTL Standard (MLTL-STD) format as input on top of its own language. The
MLTL-STD format is a simpler format for the description of sets of MLTL formulas. The files are made
up of a sequence of MLTL formulas, each terminated by a newline. The standard uses atomic
propositions of the form `a<NUMBER>` (for example, `a0`, `a5`, `a32`, etc.) and infix operators to
describe MLTL formulas. For example:

    G[0,5] a0 & (a1 U[5,10] a4)
    (a0 | a53) R[0,153] a2

R2U2 takes as input a vector of signals at each execution step. The number in each atomic
proposition symbol defines which index to read from that input vector to R2U2, e.g., the symbol `a3`
represents the value at index 3 of the input. 

See the `mltl/` directories of the `benchmarks/` for examples.