# Assume-Guarantee Contract Example

For this example, we'll be using the following input file (`agc.c2po`):

    INPUT
        b0,b1: bool;

    FTSPEC
        contract: b0 => b1;

Notice that we have a formula labeled `contract` with a formula that uses the `=>` operator. The `=>` denotes a *assume-guarantee contract*, which means that R2U2 will report whether the expression is true, false, or inactive. The contract is true if both the left and right sides of the `=>` are true, false if the left side is true and right side is false, and inactive otherwise (if the left side is false). Notice that the output of a `=>` operator is three-value: this means that it can only ever be the top-level operator of a formula. So if we had a third variable `b2`, the formula `(b0 => b1) && b2` would not be valid.

We'll use the following CSV file as simulated input (`agc.csv`):

    # b0,b1
    0,0
    1,0
    0,1
    1,1

Then compile the specification using C2PO:

    python compiler/r2u2prep.py --booleanizer agc.c2po agc.csv

And finally run using R2U2:

    ./monitors/static/build/r2u2 r2u2_spec.bin agc.csv