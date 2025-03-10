# Running

These instructions are for using the provided R2U2 CLI example; to use R2U2 as a library, see [embedding R2U2](./embedding.md).

## Prerequisites

1. [Build](./building.md) `r2u2_cli` crate
2. A C2PO specification file

:::{note} If `r2u2_cli` was built locally, run the `r2u2_cli` with following command: `./target/release/r2u2_cli`. If `r2u2_cli` was installed
from crates.io, run by simply calling `r2u2_cli`.
:::

### Use `r2u2_cli` to compile only
**<u>Usage:</u> r2u2_cli compile** [OPTIONS] \<SPEC> \<MAP>

**<u>Arguments:</u>**

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;  \<SPEC>   Sets a specification .c2po or .mltl file or spec.bin

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;  \<MAP>   Sets a trace .csv or a map .map file

**<u>Options:</u>**

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-o, -\\\-output** \<PATH>      Sets location to save output in a file (default = current directory)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-disable-booleanizer**        Disables booleanizer (default = booleanizer enabled)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-disable-aux**                Disable Assume-Guarantee Contract (AGC) and auxiliary specification logging

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-disable-rewrite**           Disables rewrite rules (default = rewrite rules enabled)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-disable-cse**                Disables common subexpression elimination (CSE) (default = CSE enabled)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-enable-sat**                 Enables SAT checking through Z3 -> Z3 must be installed (default = SAT disabled)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-timeout-sat** <TIMEOUT_SAT>  Set the timeout of SAT calls in seconds (default: 3600)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-h, -\\\-help**               Print help

### Use `r2u2_cli` to run R2U2

**<u>Usage:</u> r2u2_cli run** [OPTIONS] \<SPEC> \<TRACE>

**<u>Arguments:</u>**

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;  \<SPEC>   Sets a specification .c2po or .mltl file or spec.bin

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;  \<TRACE>  Sets a trace .csv file

**<u>Options:</u>**

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-o, -\\\-output** \<PATH>      Sets location to save output in a file (default = print to terminal)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-disable-contracts**  Disable assume-guarantee contract status logging

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-\\\-enable-aux**         Enable auxiliary specification logging

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**-h, -\\\-help**               Print help

