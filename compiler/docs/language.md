# C2PO Input Language

C2PO offers a structured specification language intended to make writing formal specifications easy
and transparent. The language is structured into a number of sections for defining inputs, C-style
structs, macros, and specifications. The most basic C2PO file is just:

    INPUT
        a: bool;

    FTSPEC
        a;

A more complex example file is:

    INPUT
        a,b: int;
    
    DEFINE
        c := a + b;

    FTSPEC
        (a > 0) -> F[0,5](c > 5);

Each section has a keyword to denote its beginning:

- `INPUT`: Input signals and their types
- `STRUCT`: C-like structs
- `DEFINE`: Macros
- `ATOMIC`: Atomics used by the atomic checker. (*Must compile with `--atomic-checker` flag.*)
- `FTSPEC`: Future-time MLTL specifications
- `PTSPEC`: Past-time MLTL specifications

Sections can be declared multiple times and are order-sensitive; in order to refer to an input `x`,
for example, you must declare it in an `INPUT` section earlier in the file.

See the example files for samples of complete, valid input. The best source for the formal syntax is
found in the [parser](../c2po/parser.py). The allowable symbols can be derived from the `C2POLexer`,
and parsing rules are found in the `C2POParser`.

## Identifiers

Identifiers are the name of any variable, struct, definition, or formula label. They must be of the
form

    [a-zA-Z_][a-zA-Z0-9_]*

The following words are reserved words and therefore cannot be used as identifiers:

    STRUCT INPUT DEFINE ATOMIC FTSPEC PTSPEC
    foreach forsome forexactly foratleast foratmost
    pow sqrt abs xor rate
    G F H O U R S M
    true false

## Types

C2PO supports `bool`, `int`, and `float` basic types and arrays. Arrays are declared using C-style
syntax, for example, `int[10]`.

C2PO also supports user-definable C-style structs. We can define a struct with members of each type
as follows:

    STRUCT
        MyStruct: {
            my_bool: bool;
            my_int: int;
            my_float: float;
            my_array: int[];
            my_array_2: int[10];
        };

Arrays in defined structs can be given either concrete or indeterminate sizes (as in `my_array` or
`my_array_2`). 

## Inputs

The `INPUT` section is where the input signals for R2U2 are defined. For example:

```
INPUT
    p,q: bool;
    i,j: int;
    x,y: float;
    A,B: int[10];
```

This defines the variables listed as you would expect and these variables are now free to be used in
any following sections. In order to know which variable corresponds to which input to R2U2, C2PO
needs a mapping of variables to input vector indices. See the page on [signal
mapping](./signal_mapping.md) for more information.

## Supported Operators

C2PO supports the following operators in the table below

| Operator Family | Operator Symbols                        | Signature                                                       | Example(s)         |
|-----------------|-----------------------------------------|-----------------------------------------------------------------|--------------------|
| Logical         | `!`                                     | `bool` $\rightarrow$ `bool`                                     | `!p`               |
|                 | `&&`, `\|\|`, `xor`, `==`, `->`, `<->`  | `bool` $\times$ `bool` $\rightarrow$ `bool`                     | `p && q`           |
| Relational      | `==`, `!=`                              | `bool` $\times$ `bool` $\rightarrow$ `bool`                     | `p == q`           |
|                 | `==`, `!=`, `>`, `<`, `>=`, `<=`        | `int` $\times$ `int` $\rightarrow$ `bool`                       | `i <= j`           |
|                 |                                         | `float` $\times$ `float` $\rightarrow$ `bool`                   | `x >= y`           |
| Arithmetic      | `-`, `sqrt`, `abs`                      | `int` $\rightarrow$ `int`                                       | `-i`, `abs(i)`     |
|                 | `-`, `abs`                              | `float` $\rightarrow$ `float`                                   | `-x`, `sqrt(y)`    |
|                 | `+`, `-`, `*`, `/`, `%`, `pow`          | `int` $\times$ `int` $\rightarrow$ `int`                        | `i + j`, `i pow j` |
|                 |                                         | `float` $\times$ `float` $\rightarrow$ `float`                  | `x * y`, `y / x`   |
| Bitwise         | `~`                                     | `int` $\rightarrow$ `int`                                       | `~i`               |
|                 | `&`, `\|`, `^`, `<<`, `>>`              | `int` $\times$ `int` $\rightarrow$ `int`                        | `i << j`, `i & j`  |
| Future-time     | `G`, `F`,                               | `interval` $\times$ `bool` $\rightarrow$ `bool`                 | `G[0,5] p`         |
|                 | `U`, `R`                                | `bool` $\times$ `interval` $\times$ `bool` $\rightarrow$ `bool` | `p U[3,7] q`       |
| Past-time       | `H`, `O`                                | `interval` $\times$ `bool` $\rightarrow$ `bool`                 | `H[2,6] p`         |
|                 | `S`                                     | `bool` $\times$ `interval` $\times$ `bool` $\rightarrow$ `bool` | `p S[0,5] q`       |
| Array Index     | `[]`                                    | `array` $\times$ `int` $\rightarrow$ `array element type`       | `A[4]`             |

Equality/inequality checks between floats are performed in R2U2 with respect to a value $\epsilon$,
i.e., `x == y` will be true if $\vert x - y \vert > \epsilon$. This value is set in R2U2 in
[bounds.h](../montors/static/src/internals/bounds.h) via `R2U2_FLOAT_EPSILON`.

Some operators require their arguments to be constants. Division (`/`) requires the right-hand side
to be constant to avoid division-by-zero errors at runtime and the power operator (`pow`) requires
the right-hand side to be constant to avoid negative exponents. Array indexes must be a simple
numeral, no compound, non-constant expressions are allowed.

### Set Aggregation

C2PO also supports *set aggregation*. These operators take a symbol name, array, and expression as
arguments, applying a conjunction/disjunction to the argument expression for every value in the
array. For example, to state that every value in `A` is greater than 0: 

    foreach(k: A)(k > 0);

During compilation this is expanded to (where `n` is the size of `A`):

    (A[0] > 0) && (A[2] > 0) && ... && (A[n] > 0);

C2PO supports `foreach` and `forsome` operators. `forexactly`, `foratleast`, and `foratmost` are
reserved words for future use.

## Definitions

The `DEFINE` section allows users to define named expressions. These are essentially treated as
macros that replace each occurrence of the named expression with its definition during compilation.
Definitions are of the form:

    symbol := expression ;

For example, using the inputs defined above:

    DEFINE
        r := p && q;
        k := i + j;
        z := x / z;

## Specifications

The `FTPSEC` and `PTSPEC` sections are where specifications for monitoring go. A specification can
be any expression of `bool` type. For example:

    FTSPEC
        p U[0,5] q;
        F[0,5] (i > j);

    PTSPEC
        O[0,5] (x < y);

In ths example, the specification `p U[0,5] q` has ID 0, `F[0,5] (i > j)` has ID 1, and `O[0,5] (x <
y)` has ID 2. Then if R2U2 outputs `1:3,T` this means that the specification with ID 1 is true at
time 3.

### Specification Labels

Specifications can have optional labels. This allows them to be used in other specifications. If
R2U2 is compiled with the `R2U2_TL_Formula_Names`, then R2U2 will also output the labels in place of
the ID. For example:

    FTSPEC
        label:   F[0,3] p;
        label_2: G[0,3] q && label;

### Assume-Guarantee Contracts

*(R2U2 must be compiled with the `R2U2_TL_Contract_Status` option enabled)*

Specifications can also be in the form of assume guarantee contracts (AGCs). AGCs are required to
have a label and are of the form `assume => guarantee`. They are only allowed to be the top-level
operator of a specification. For example:

    FTSPEC
        contract: p => q;

R2U2 will output `inactive` if `p` is false, `invalid` if `p` is true and `q` is false, and
`verified` if both `p` and `q` are true.

## Atomic Checkers

If the Atomic Checker engine is enabled, then `int` an `float` inputs can be transformed into `bool`
values using "atomic checkers". An atomic checker is a structured expression of the form:

    atomic := input <relational operator> constant;

Atomic checkers are defined in the `ATOMIC` section of a file. For example:

    ATOMIC
        a0 := i > 5;
        a1 := x <= 3.6;

Atomic checkers are largely useful for the hardware version of R2U2.