# R2U2 Front End Selection
R2U2 supports two different engines for reasoning about non-Boolean data: Atomic Checkers and the Booleanizer. Atomic checkers are more restricted in their syntax and are supported for both the hardware and software versions of R2U2. The Booleanizer is a general purpose engine only supported in the static version of R2U2 and is generally more memory and time intensive. 

*You must select exactly one front-end when compiling a specification.* In practice this means that one of ` --atomic-checker` or ` --booleanizer` flags must be set for any call to C2PO. 

## Booleanizer
The booleanizer is a general purpose engine that can perform arithmetic, bitwise operations, parameterized set aggregation (`foratleast`, etc.), and other such capabilities. 

## Atomic Checker
Atomic checkers are the names for the relational expression seen in `examples/atomic_checker.mltl`. They allow for the filtering of signals and then comparing the output of that signal to a constant or other signal. This is particularly useful in hardware, but is available in the software version of R2U2 as well.

### Available Filters:
- `rate`: `(float)` -> `float`
    - Rate of change between time steps
- `movavg`: `(float,int)` -> `float`
    - Moving average with window size `int` (max window size is 5 by default)
- `abs_diff_angle`: `(float,float)` -> `float`
    - Absolute difference between the arguments if both treated as angles.
