Contract Status

Using R2U2 expanded output:
 
R2U2 supports two extended output modes:
  *) Named formula output
  *) Contract Status
They can be enabled at compile time by setting the macros
`R2U2_TL_Formula_Names` and `R2U2_TL_Contract_Status`
respectively. These can either be set as define flags
(e.g. `-DR2U2_TL_Formula_Names`) or by adding a define
to the R2U2Config.h file (e.g. `#define R2U2_TL_Formula_Names 1`).
 
If either of these features are enabled the function `TL_aux_config`
is run in R2U2.c, make sure to run this yourself if and only if you are using
one of these features and you aren't using the example main function.
 
The `TL_aux_config` function takes a path to the alias file relative to the
binaries directory specified at runtime.
 
The alias file used a fixed format where each line is a record starting with
a one character record type then white space separated fields depending on the
type.
 
For Formula Names:
Records start with 'F' and are contain the name and formula number. E.g:
```
F Foo 1
F Bar 7
F Hello 5
```
In the output log, any formulas with a defined name will print that instead of
the formula number in the verdicts. For example:
```
3:0,T
Bar:0,F
```
 
 
For Contract Status:
To output tri-state contact status a record of the form:
C Name 1 2 3
is needed where the numbers refer to the formula numbers of the assume,
implication, and conjunction of the contract respectively.
For example, for the contract "assume Foo guarantees Bar" where:
  - Formula 2: Foo;
  - Formula 4: Foo -> Bar;
  - Formula 3: Foo & Bar;
The contract definition will be:
`C FooBar 2 4 3`
 
This will case an output on standard out with the form:
"Contract <Name> <Status> at <Time>"
Where Status is one of:
  - Inactive - the assume is false
  - Violated - the contract failed
  - Verified - the contract was upheld