# Output

Results are given as a verdict stream. 
As a CLI program this is written to standard out by default but can be re-directed to an output file with the -\\\-output \<PATH> option.
As a library, `r2u2_core` provides the function `get_output_buffer` and `get_contract_buffer`. More information on `r2u2_core` output function available at [https://docs.rs/r2u2_core/latest/r2u2_core/](https://docs.rs/r2u2_core/latest/r2u2_core/).

## Verdict Stream

Verdicts are output one per line as the formula id number (indexing from 0), followed by a colon and then the verdict tuple. The verdict tuple consists of an integer timestamp and a literal “T” or “F” to mark the truth value. The asynchronous monitors produce aggregated output — that is, if they can determine a range of values with the same truth at once, only the last time is output. In the example below, formula with ID 2 is false from time 8-11 inclusive.

```
2:7,T
5:4,F
2:11,F
```