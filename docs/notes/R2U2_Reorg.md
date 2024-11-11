# R2U2 Reorg

Run Time Step
Spin Once
Step

R2U2
  |
Modules: Temporal, Atomic, Predictive


Memory:
Init: Setup
Run:
Exit:

Headers:
  R2U2.h - external library functions
  R2U2Config.h
  R2U2Memory.h
  R2U2Defs.h

Definition order:
  R2U2 Memory
  R2U2 Defs
    - per-module defs
    * R2U2 Struct
  Toplevel Headers


TODO:
  - Parameterize all types
  - Verify all headers are required
  - Fix parse/config (add builtin, accept paths, etc.
  - Promote major vectors to top level with handle API (signals, atomics, etc.)