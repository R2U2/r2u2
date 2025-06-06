# Signal Trace Files [`.csv`]

A signal trace file is a UTF-8 encoded text file with a `.csv` extension that beings with a header line followed by one or more record lines that specify the values of the signals named in the header at each timestep.

The required header is denoted with a ‘#’ character as the first character of the line followed by comma-separated signal names for each "column" of the signal trace.

The record lines are comma-separated signal values in the same order as named in the header.
Each line represents one time-step, but this is a logical clock and the actual elapsed time between records is not specified.

For example:
```
# p,q,i,j,k
0,1,5,2,3
0,0,4,2,3
1,1,2,6,10
```

One can also define multiple time-steps in a single line, where `@T` is the signal at `T` and since the last `@` symbol. For example,
the following:
```
# p,q,i,j,k
0,1,5,2,3
0,1,5,2,3
0,1,5,2,3
0,0,4,2,3
0,0,4,2,3
1,1,2,6,10
```
can also be represented as (note that time starts at 0):
```
# p,q,i,j,k
@2 0,1,5,2,3
@4 0,0,4,2,3
@5 1,1,2,6,10
```