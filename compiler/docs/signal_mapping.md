# Signal Mapping

At runtime, R2U2 takes as input a vector of signals at each execution step. This vector represent
the value of each signal at the corresponding timestamp. In order to associate those inputs to the
variables defined in a C2PO file, we have to provide a mapping of variable names to indices in that
signals vector.

All variable symbols in a C2PO file that are referenced in a specification must be mapped to an
index, otherwise C2PO will report an error. C2PO provides two ways to provide a mapping: a map or a
trace file.

## Map File

A map file directly associates an index with a variable symbol and traditionally has a `.map` file
extension. Each line of the input file is of the form 

    symbol : numeral 

If `symbol` corresponds to a variable symbol in the C2PO file, its signal index is set to the value
of `numeral`. If `symbol` is not present in the C2PO file, the line is ignored. Repeat signal
indices are allowed, if you want two variables to map to the same input. As an example:

    p:0
    q:1
    i:2
    j:3
    k:2

At each step of R2U2, the value at index 0 will be interpreted as `p` and so on for each other
symbol. Also, this file is such that `i` and `k` will have the same input signal. Importantly, the
type of the value in the signals vector should match the type defined in the C2PO file. If `i`, `j`,
and `k` are `int`s, then their values in the signal vector must also be of `int` type.

Remember that C2PO also supports input arrays, including things like `Array: int[3];`. To map these
inputs, we provide a mapping for each index in the array:

    Array[0]:0
    Array[1]:1
    Array[2]:2

## Trace File

Alternatively, if you are using R2U2 in offline mode and using a `.csv` file as input to R2U2, it
may be convenient to use that same file for signal mapping. For this we use the first line in the
`.csv` file as a header to define which column corresponds to which variable. The first line must
start with a `#` character then be followed by a comma-separated list of each variable in the C2PO
file. For example

    # p,q,i,j,k
      0,1,5,2,3
      0,0,4,2,3
      1,1,2,6,10

