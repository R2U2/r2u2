# Signal Trace Files [`.csv`]

A signal trace file is a UTF-8 encoded text file with a `.csv` extension that beings with a header line followed by one or more record lines that specify the values of the signals named in the header at each timestep.

The required header is denoted with a ‘#’ character as the first character of the line followed by comma-separated signal names for each "column" of the signal trace.

The record lines are comma-separated signal values in the same order as named in the header.
Each line represents one time-step, but this is a logical clock and the actual elapsed time between records is not specified.

For example:
```
# sig0,sig1
0,1
```
