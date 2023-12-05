# MLTL-STD
The MLTL-STD format is a standardized format for the description of sets of MLTL formulas. The files are made up of a sequence of MLTL formulas, each terminated by a newline. MLTL formulas are made up of atomic propositions of the form `a<NUMBER>` (for example, `a0`, `a5`, `a32`, etc.), or infix operators. For example:

    G[0,5] a0 & (a1 U[5,10] a4)
    (a0 | a53) R[0,153] a2

See the `mltl/` directories in [](../../benchmarks/) for more examples.