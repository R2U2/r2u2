# Optimizations

C2PO supports a number of optimizations for MLTL specifications that can reduce the encoding size of
observers. Importantly, these optimizations will either reduce or maintain the encoding size of a
specification. Common sub-expression elimination and rewrite rules are enabled by default, while
equality saturation is optional.

## Common Sub-expression Elimination
*(Enabled by default. Disable with `--no-cse`; enable explicitly with `--cse`.)*

This optimization enables sharing of common sub-expression across specifications. As an example,
notice the sub-expression `G[0,5] a0` in the following specification:

    (G[0,5] a0) & (F[0,10] a1)
    (G[0,5] a0) | (a0 U[0,10] a2)

We could naively compile this and generate two separate observers for both instances of `G[0,5]a0`;
but using CSE we can notice that these two instances are equivalent, so they can share the output of
a single observer. 

Under the hood, C2PO is traversing the syntax tree of the specification, keeping track of all
expressions seen so far, and checking if it has seen the current expression earlier. This is a
syntactic check, so each expression is hashed by its string representation for (relatively)
efficient lookup.

## Rewrite Rules
*(Enabled by default. Disable with `--no-rewrite`; enable explicitly with `--rewrite`.)*

Formula rewriting does a single traversal of the expression tree and performs the rewrites found in
the [2023 FMICS paper](https://research.temporallogic.org/papers/JKJRW23.pdf). C2PO does a single
pass of the expression tree, applying rewrite rules on valid expressions that match a given pattern.
One rewrite rule "factors out" `G`/`F` operators:  

$$ \Box_{[a,b]} \varphi \land \Box_{[c,d]} \psi \mapsto \Box_{[e,f]}(\Box_{[a-e,b-f]} \varphi \land
    \Box_{[c-e,d-f]} \psi) $$

where $e = min(a,b)$ and $f = e + min(b-a,d-c)$. For example:

    (G[0,5] a0) & (G[0,8] a1) ===> G[0,5] (a0 & (G[0,3] a1)) 

This rewrite reduces the encoding size of this formula since memory for each sub-expression is
dependent on the *worst-case propagation delay* (wpd) of its siblings. The sibling node of `(G[0,5]
a0)` is `(G[0,8] a1)`, which has a wpd of 8. In its rewritten form, the sibling node of `a0` is
`G[0,3] a1` which has a wpd of 3.

## Equality Saturation
*(Disabled by default. Enable with `--eqsat`; disable with `--no-eqsat`.)*

**This optimization requires [egglog](https://github.com/egraphs-good/egglog) to be installed. See the requirements section of the README.**

Equality saturation applies the formula rewrites above in a systematic way, resulting in a maximally
reduced monitor encoding. The technique is described fully in [Chapter 4 of this
thesis](https://cgjohannsen.com/docs/ms-thesis.pdf). It uses
[egglog](https://github.com/egraphs-good/egglog) to compute the minimally-sized encoding of each
formula with respect to a set of pre-defined rewrites.

The following CLI options control EQSat behavior:

- `--eqsat-max-time` / `--eqsat-max-memory`: resource limits for egglog
- `--egglog-path`: explicit path to the egglog binary
- `--eqsat-check-equiv`: check equivalence of EQSat results
- `--eqsat-const-folding`, `--eqsat-associative`, `--eqsat-commutative`, `--eqsat-multi-arity`, `--eqsat-temporal`: enable or disable specific rewrite families (each also supports a `--no-...` form)

This feature currently only runs on each formula individually. There are plans to extend this
feature to this feature to the [entire formula set](https://github.com/R2U2/r2u2/issues/8).

## Extended Operators

***(Unsupported by R2U2)***

*(Disabled by default. Enable with `--extops`; disable with `--no-extops`.)*

By default, R2U2 supports only the negation, conjunction, global, and until MLTL operators. C2PO
allows unsupported operators (like disjunction) in its input but replaces them with the equivalent
expression in MLTL using only officially supported operators. For example, the expression

    F[0,5] (a || b)

would be rewritten to

    ! G[0,5] ! (!a && !b)

without enabling extended operators. R2U2 does support the full range of MLTL operators natively if
compiled with the correct option. 