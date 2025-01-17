# Project Structure
> Directory of repository layout and descriptions of other available documentation

This repository is structured as a mono-repo containing multiple sub-projects that all interact to provide an ecosystem for developing and monitoring MLTL formulas.

The files are organized as follows:


benchmarks
: Sets of MLTL benchmarks from industrial case studies and publications


compiler
: The C2PO formula compiler, produces specification configuration for R2U2 monitors


docs
: Framework-wide documentation, builds a combined documentation containing sub-project and project-wide components


examples
: Examples of MLTL formulas highlighting various C2PO and R2U features


monitors
: Implementations of the R2U2 monitor, currently only C is supported


test
: Integration regression testing of C2PO and R2U2 end-to-end
