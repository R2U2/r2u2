# MLTL Optimizations
C2PO supports a number of optimizations for MLTL specifications that can reduce the encoding size of observers. Importantly, these optimizations **will either reduce or maintain the encoding size of a specification**. Each is on by default, but can be disabled by running its corresponding flag.

## Common Sub-expression Elimination 
(To disable, use the `--disable-cse` flag)

This optimization enables sharing of common sub-expression across specifications. As an example, notice the sub-expression `G[0,5]a0` in the following specification:

    (G[0,5] a0) & (F[0,10] a1)
    (G[0,5] a0) | (a0 U[0,10] a2)

We could naively compile this and generate two separate observers for both instances of `G[0,5]a0` -- but using CSE we can notice that these two instances are equivalent, so they can share the output of a single observer. 

Under the hood, C2PO is traversing the syntax tree of the specification, keeping track of all expressions seen so far, and checking if it has seen the current expression earlier. This is a syntactic check, so each expression is hashed by its string representation for (relatively) efficient lookup.

## Rewrite Rules
(To disable, use the `--disable-rewrite` flag)

This optimization does a single pass of the expression tree, applying rewrite rules on valid expressions that match a given pattern. One rewrite rule "factors out" `G`/`F` operators:  

$$
    \Box_{[a,b]} \varphi \land \Box_{[c,d]} \psi \mapsto 
    \Box_{[e,f]}(\Box_{[a-e,b-f]} \varphi \land \Box_{[c-e,d-f]} \psi)
$$

where $e = min(a,b)$ and $f = e + min(b-a,d-c)$. For example:

    (G[0,5] a0) & (G[0,8] a1) ===> G[0,5] (a0 & (G[0,3] a1)) 

This rewrite reducing the encoding size of this formula since memory for each sub-expression is dependent on the *worst-case propagation delay* (wpd) of its siblings. The sibling node of `(G[0,5] a0)` is `(G[0,8] a1)`, which has a wpd of 8. In its rewritten form, the sibling node of `a0` is `G[0,3] a1` which has a wpd of 3.