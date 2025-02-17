# Simple Example
Let's start with a very simple example with a single temporal formula with a single Boolean variable. This is the C2PO file named `simple.c2po` we'll be working with:
```
INPUT
    a0,a1: bool;

FTSPEC
    F[0,2] (a0 && a1);
```
Note that we first declare `a0` to be an input with type `bool`, then define a specification that states that `a0` will be true at least once between "now" and 2 timestamps from "now." Note that "now" is a moving window -- we'll see this after we monitor our simulated trace, in a file named `simple.csv`:
```
# a0,a1
1,1
0,0
1,1
0,0
1,0
0,0
```
This trace is a csv file where the first line is a header (denoted by the `#` first character) that lists the input variables used in the specification. Each following line defines the values of each input for each timestamp. For example, `a0` is `true ` and `a1` is `false ` at timestamp 4 (since timestamps are indexed starting at 0).

We can then compile our specification using the following command:
```bash
python compiler/c2po.py --booleanizer simple.mltl --trace simple.csv
```
The `--booleanizer` flag enables the Booleanizer engine, which computes non-Boolean operations (for example, addition, multiplication, comparisons, etc.). This command will generate a file named `spec.bin` that is a binary encoding of the specification for `r2u2`.

And finally run using R2U2 C version:

    ./monitors/c/build/r2u2 spec.bin simple.csv

Or R2U2 Rust version:

    ./monitors/rust/r2u2_cli/target/release/r2u2_cli run spec.bin agc.csv