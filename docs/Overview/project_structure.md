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


GUI
: A web interfaces for visualizing MLTL formula sets


logs
: Verified output of the provided examples


monitors
: Implementations of the R2U2 monitor, currently only static is supported


run_examples.sh
: Runs all examples and compares to the gold-standard logs


test
: Integration regression testing of C2PO and R2U2 end-to-end


tools
: Small scripts for working with MLTL inputs and outputs
