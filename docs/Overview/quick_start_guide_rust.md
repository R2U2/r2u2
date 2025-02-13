# Quick-Start Guide (Rust Version)

## Dependencies

- Posix environment (Linux, MacOS, Etc.)
- Python3 (version 3.8 or greater)
- [Rust](https://www.rust-lang.org/tools/install) 1.82.0 or greater

# Installing

There is a [r2u2_cli](https://crates.io/crates/r2u2_cli) Rust crate available to run C2PO and R2U2.
To install:
```bash
cargo install r2u2_cli
```

# Running

Running R2U2 requires a **specification** and an **input stream**.

1. Write the following specification to a file named `simple.c2po`:

        INPUT
            request, grant: bool;

        FTSPEC
            -- If a request is made, it shall be granted within 5 time steps.
            request -> F[0,5] grant;

2. Provide a mapping for variables to signal indices in a file named `simple.map`:

        request:0
        grant:1

4. Write a simulated trace to monitor in a file named `simple.csv`, where the first column are the
   values of `request` and the second are the values of `grant`:

        1,0
        0,0
        0,1
        0,0
        1,0
        0,0
        0,0
        0,0
        0,0
        0,0

5. Run C2PO and R2U2 using the specification and the input stream:
        
        r2u2_cli run simple.c2po simple.csv

## Output

The output of R2U2 is a *verdict stream* with one verdict per line. A verdict includes a **formula
ID**, **timestamp**, and **truth value**. Formula IDs are determined by the order in which they are
defined in the specification file.  Verdicts are *aggregated* so that if R2U2 can determine a range
of values with the same truth at once, only the last time is output.

The following is a stream where formula 0 is true from 0-7 and false from 8-11 and formula 1 is
false from times 0-4:

        0:7,T
        1:4,F
        0:11,F
