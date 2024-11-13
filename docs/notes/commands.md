# Commands
## File Loading
- `load-mltl <filename>`
- `load-c2po <filename>`
- `load-trace <filename>`
- `load-map <filename>`

## Compiling/Execution
- `compile-spec`
- `compile-monitor`
- `run`

## Trace generation
- `set-trace-seed <int>`
- `gen-unsat-trace`
- `gen-sat-trace [full, random, median]`

## WEST
- `gen-regex`
- `filter-regex <regex>`

## C2PO Data Saves
- `save-ast <filename>`
- `save-mltl <filename>`
- `save-c2po <filename>`


## C2PO/R2U2 Options
- `set-impl [c, cpp, vhdl]`
- `set-int-width <int>`
- `set-int-signed [0,1]`
- `set-float-width <int>`
- `set-float-epsilon <float>`
- `set-atomic-checkers [0,1]`
- `set-booleanizer [0,1]`
- `set-extops [0,1]`
- `set-max-atomics <int>`
- `set-max-signals <int>`
- `set-max-instr <int>`
- `set-max-instr_len <int>`
- `set-max-tl-instr <int>`
- `set-max-at-instr <int>`
- `set-max-bz-instr <int>`
- `set-max-aux-strs <int>`
- `set-max-boxq-bytes <int>`
- `set-max-scq-bytes <int>`


### C2PO Options
- `set-binary-output <filename>`
- `set-mission-time <int>`
- `set-cse [0,1]`
- `set-rewrite [0,1]`
