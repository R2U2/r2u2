# UAS Traffic Management Benchmarks

Benchmarks adapted from [Integrating Runtime Verification into an Automated UAS Traffic Management System](https://research.temporallogic.org/papers/CHHJR20.pdf). The specifications are listed at this [webpage](https://temporallogic.org/research/DETECT2020/results.html) and were cleaned from the HTML source and all placed in a single file.

`utm/mltl` contains all specifications with labels in a single file, and all other files are single specifications with their filename as their label.

The trace files include only the header so the corresponding `mltl` file can be compiled.

We assume a 45 minute mission time (2700 seconds), since it is not defined in the paper but the plots in the paper appear to stop at around 2700 seconds.