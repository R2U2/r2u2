# Output

Results are returned as a text called the verdict stream and written to a file descriptor.
As a CLI program this is written to standard out, when embedded as a library the output file is set in the monitor.
Additionally, the monitor takes a result callback function pointer to allow arbitrary user-defined behavior whenever a result is returned.

## Verdict Stream

Verdicts are output one per line as the formula id number (indexing from 0), followed by a colon and then the verdict tuple. The verdict tuple consists of an integer timestamp and a literal “T” or “F” to mark the truth value. The asynchronous monitors produce aggregated output — that is, if they can determine a range of values with the same truth at once, only the last time is output. In the example below, formula with ID 2 is false from time 8-11 inclusive.

```
2:7,T
5:4,F
2:11,F
```

## Results Callback

If set in the monitor, the user defined function `r2u2_status_t (*out_func)(r2u2_instruction_t, r2u2_verdict*)` will be called by the temporal logic engine for each result.
It includes the instruction that generated the result as well as the verdict as arguments and expects an R2U2 Status enum varient as a return type.
This can be used to provide custom output handling link message publishing or database storage.

## Logging

Additional information on the internal monitor state is enabled by the [logging feature flags](./configuration.md#logging-output).

### Debug
The debug logging level provides information about the internal control flow and some memory integrity checks.
It can be helpful when debugging a new R2U2 deployment and should be included in any bug reports about monitor behavior.
It is written to `FILE* r2u2_debug_fptr` which is externally linked from the debug routine and must be set (usually in `lib.c` or `cli/main.c`) prior to use.
By default `r2u2_debug_fptr` is set to standard error when building R2U2 as a CLI program.

### Trace
Memory trace logging adds even more verbose output and always writes to standard error is enable - this is only for development of the R2U2 monitor itself.
