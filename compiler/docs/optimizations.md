# Optimizations

C2PO supports a number of optimizations for MLTL specifications that can reduce the encoding size of
observers. Importantly, these optimizations will either reduce or maintain the encoding size of a
specification. Both CSE and rewriting are enabled by default, all others must be enabled manually.

## Common Sub-expression Elimination
*(To disable, use the `--disable-cse` flag)*

This optimization enables sharing of common sub-expression across specifications. As an example,
notice the sub-expression `G[0,5]a0` in the following specification:

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
*(To disable, use the `--disable-rewrite` flag)*

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
*(To enable, use the `--enable-eqsat` flag)*

**This optimization requires [egglog](https://github.com/egraphs-good/egglog) to be installed. See the requirements section of the README.**

Equality saturation applies the formula rewrites above in a systematic way, resulting in a maximally
reduced monitor encoding. The technique is described fully in [Chapter 4 of this
thesis](https://cgjohannsen.com/docs/ms-thesis.pdf). It uses [egglog](https://github.com/egraphs-good/egglog) to 

## Extended Operators

***(Unsupported by R2U2)***

*(To enable, use the `--extops` flag)*

By default, R2U2 supports only the negation, conjunction, global, and until MLTL operators. C2PO
allows unsupported operators (like disjunction) in its input but replaces them with the equivalent
expression in MLTL using only officially supported operators. For example, the expression

    F[0,5] (a || b)

would be rewritten to

    ! G[0,5] ! (!a && !b)

without enabling extended operators. R2U2 does support the full range of MLTL operators natively if
compiled with the correct option. 