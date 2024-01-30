from __future__ import annotations

from typing import Callable, Optional, cast

from c2po import cpt, log, types

MODULE_CODE = "TRNS"


def transform_definitions(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms each definition symbol in the definitions and specifications of `program` to its expanded definition. This is essentially macro expansion."""
    log.debug("Expanding definitions", MODULE_CODE)

    for expr in [
        expr
        for define in context.definitions.values()
        for expr in cpt.postorder(define, context)
    ] + [expr for expr in program.postorder(context)]:
        if not isinstance(expr, cpt.Variable):
            continue

        if expr.symbol in context.definitions:
            expr.replace(context.definitions[expr.symbol])
        elif expr.symbol in context.specifications:
            expr.replace(context.specifications[expr.symbol].get_expr())

    log.debug(f"Post definition expansion:\n{program}", MODULE_CODE)


def transform_function_calls(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms each function call in `program` that corresponds to a struct instantiation to a `ast.C2POStruct`."""
    for expr in [
        expr
        for define in context.definitions.values()
        for expr in cpt.postorder(define, context)
    ] + [expr for expr in program.postorder(context)]:
        if not isinstance(expr, cpt.FunctionCall):
            continue

        if expr.symbol not in context.structs:
            continue

        struct_members = [m for m in context.structs[expr.symbol].keys()]
        expr.replace(
            cpt.Struct(
                expr.loc,
                expr.symbol,
                {
                    name: struct_members.index(name)
                    for name in context.structs[expr.symbol].keys()
                },
                expr.children,
            )
        )


def transform_contracts(program: cpt.Program, context: cpt.Context) -> None:
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""
    log.debug("Replacing contracts", MODULE_CODE)

    for contract in [
        spec for spec in program.get_specs() if isinstance(spec, cpt.Contract)
    ]:
        new_formulas = [
            cpt.Formula(
                contract.loc,
                f"__{contract.symbol}_active__",
                contract.formula_numbers[0],
                contract.get_assumption(),
            ),
            cpt.Formula(
                contract.loc,
                f"__{contract.symbol}_valid__",
                contract.formula_numbers[1],
                cpt.LogicalImplies(
                    contract.loc, contract.get_assumption(), contract.get_guarantee()
                ),
            ),
            cpt.Formula(
                contract.loc,
                f"__{contract.symbol}_verified__",
                contract.formula_numbers[2],
                cpt.LogicalAnd(
                    contract.loc, [contract.get_assumption(), contract.get_guarantee()]
                ),
            ),
        ]

        new_formulas = cast("list[cpt.Specification]", new_formulas)

        program.replace_spec(contract, new_formulas)

        log.debug(f"Replaced contract '{contract.symbol}'", MODULE_CODE)


def transform_set_aggregation(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction."""
    log.debug("Unrolling set aggregation expressions", MODULE_CODE)

    def resolve_struct_accesses(expr: cpt.Expression, context: cpt.Context) -> None:
        for subexpr in cpt.postorder(expr, context):
            if not isinstance(subexpr, cpt.StructAccess):
                continue

            struct = subexpr.get_struct()
            if not isinstance(struct, cpt.Struct):
                continue

            member = struct.get_member(subexpr.member)
            if member:
                subexpr.replace(member)

    for expr in program.preorder(context):
        if isinstance(expr, cpt.ForEach):
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.LogicalAnd(
                expr.loc,
                [
                    cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                    for e in expr.get_set().children
                ],
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif isinstance(expr, cpt.ForSome):
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.LogicalOr(
                expr.loc,
                [
                    cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                    for e in expr.get_set().children
                ],
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif isinstance(expr, cpt.ForExactly):
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Equal(
                expr.loc,
                cpt.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif isinstance(expr, cpt.ForAtLeast):
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.GreaterThanOrEqual(
                expr.loc,
                cpt.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif isinstance(expr, cpt.ForAtMost):
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.LessThanOrEqual(
                expr.loc,
                cpt.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)


def transform_struct_accesses(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms struct access operations to the underlying member expression."""
    log.debug("Resolving struct accesses", MODULE_CODE)
    # log.debug(f"{program}", MODULE_CODE)

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.StructAccess):
            continue

        s: cpt.Struct = expr.get_struct()
        member = s.get_member(expr.member)
        if member:
            expr.replace(member)


def transform_extended_operators(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms specifications in `program` to remove extended operators (or, xor, implies, iff, release, future)."""

    for expr in program.postorder(context):
        if isinstance(expr, cpt.LogicalOperator):
            if isinstance(expr, cpt.LogicalOr):
                # p || q = !(!p && !q)
                expr.replace(
                    cpt.LogicalNegate(
                        expr.loc,
                        cpt.LogicalAnd(
                            expr.loc,
                            [cpt.LogicalNegate(c.loc, c) for c in expr.children],
                        ),
                    )
                )
            elif isinstance(expr, cpt.LogicalXor):
                lhs: cpt.Expression = expr.children[0]
                rhs: cpt.Expression = expr.children[1]
                # p xor q = (p && !q) || (!p && q) = !(!(p && !q) && !(!p && q))
                expr.replace(
                    cpt.LogicalNegate(
                        expr.loc,
                        cpt.LogicalAnd(
                            expr.loc,
                            [
                                cpt.LogicalNegate(
                                    expr.loc,
                                    cpt.LogicalAnd(
                                        expr.loc,
                                        [lhs, cpt.LogicalNegate(rhs.loc, rhs)],
                                    ),
                                ),
                                cpt.LogicalNegate(
                                    expr.loc,
                                    cpt.LogicalAnd(
                                        expr.loc,
                                        [cpt.LogicalNegate(lhs.loc, lhs), rhs],
                                    ),
                                ),
                            ],
                        ),
                    )
                )
            elif isinstance(expr, cpt.LogicalImplies):
                lhs: cpt.Expression = expr.children[0]
                rhs: cpt.Expression = expr.children[1]
                # p -> q = !(p && !q)
                expr.replace(
                    cpt.LogicalNegate(
                        expr.loc,
                        cpt.LogicalAnd(lhs.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]),
                    )
                )
            elif isinstance(expr, cpt.LogicalIff):
                lhs: cpt.Expression = expr.children[0]
                rhs: cpt.Expression = expr.children[1]
                # p <-> q = !(p && !q) && !(p && !q)
                expr.replace(
                    cpt.LogicalAnd(
                        expr.loc,
                        [
                            cpt.LogicalNegate(
                                expr.loc,
                                cpt.LogicalAnd(
                                    lhs.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]
                                ),
                            ),
                            cpt.LogicalNegate(
                                expr.loc,
                                cpt.LogicalAnd(
                                    lhs.loc, [cpt.LogicalNegate(lhs.loc, lhs), rhs]
                                ),
                            ),
                        ],
                    )
                )
        elif isinstance(expr, cpt.Release):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            bounds: types.Interval = expr.interval
            # p R q = !(!p U !q)
            expr.replace(
                cpt.LogicalNegate(
                    expr.loc,
                    cpt.Until(
                        expr.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    ),
                )
            )
        elif isinstance(expr, cpt.Future):
            operand: cpt.Expression = expr.children[0]
            bounds: types.Interval = expr.interval
            # F p = True U p
            expr.replace(
                cpt.Until(
                    expr.loc, cpt.Bool(expr.loc, True), operand, bounds.lb, bounds.ub
                )
            )


def transform_boolean_normal_form(program: cpt.Program, context: cpt.Context) -> None:
    """Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators."""

    for expr in program.postorder(context):
        if isinstance(expr, cpt.LogicalOr):
            # p || q = !(!p && !q)
            expr.replace(
                cpt.LogicalNegate(
                    expr.loc,
                    cpt.LogicalAnd(
                        expr.loc, [cpt.LogicalNegate(c.loc, c) for c in expr.children]
                    ),
                )
            )
        elif isinstance(expr, cpt.LogicalImplies):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p -> q = !(p && !q)
            expr.replace(
                cpt.LogicalNegate(
                    expr.loc,
                    cpt.LogicalAnd(expr.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]),
                )
            )
        elif isinstance(expr, cpt.LogicalXor):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p xor q = !(!p && !q) && !(p && q)
            expr.replace(
                cpt.LogicalAnd(
                    expr.loc,
                    [
                        cpt.LogicalNegate(
                            expr.loc,
                            cpt.LogicalAnd(
                                lhs.loc,
                                [
                                    cpt.LogicalNegate(lhs.loc, lhs),
                                    cpt.LogicalNegate(rhs.loc, rhs),
                                ],
                            ),
                        ),
                        cpt.LogicalNegate(lhs.loc, cpt.LogicalAnd(lhs.loc, [lhs, rhs])),
                    ],
                )
            )
        elif isinstance(expr, cpt.Future):
            operand: cpt.Expression = expr.children[0]
            bounds: types.Interval = expr.interval
            # F p = True U p
            expr.replace(
                cpt.Until(
                    expr.loc,
                    cpt.Bool(operand.loc, True),
                    operand,
                    bounds.lb,
                    bounds.ub,
                )
            )
        elif isinstance(expr, cpt.Global):
            operand: cpt.Expression = expr.children[0]
            bounds: types.Interval = expr.interval
            # G p = !(True U !p)
            expr.replace(
                cpt.LogicalNegate(
                    expr.loc,
                    cpt.Until(
                        expr.loc,
                        cpt.Bool(operand.loc, True),
                        cpt.LogicalNegate(operand.loc, operand),
                        bounds.lb,
                        bounds.ub,
                    ),
                )
            )
        elif isinstance(expr, cpt.Release):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            bounds: types.Interval = expr.interval
            # p R q = !(!p U !q)
            expr.replace(
                cpt.LogicalNegate(
                    expr.loc,
                    cpt.Until(
                        expr.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    ),
                )
            )


def transform_negative_normal_form(program: cpt.Program, context: cpt.Context) -> None:
    """Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals."""

    for expr in program.postorder(context):
        if isinstance(expr, cpt.LogicalNegate):
            operand = expr.children[0]
            if isinstance(operand, cpt.LogicalNegate):
                # !!p = p
                expr.replace(operand.children[0])
            if isinstance(operand, cpt.LogicalOr):
                # !(p || q) = !p && !q
                expr.replace(
                    cpt.LogicalAnd(
                        expr.loc,
                        [cpt.LogicalNegate(c.loc, c) for c in operand.children],
                    )
                )
            if isinstance(operand, cpt.LogicalAnd):
                # !(p && q) = !p || !q
                expr.replace(
                    cpt.LogicalOr(
                        expr.loc,
                        [cpt.LogicalNegate(c.loc, c) for c in operand.children],
                    )
                )
            elif isinstance(operand, cpt.Future):
                bounds: types.Interval = operand.interval
                # !F p = G !p
                expr.replace(
                    cpt.Global(
                        expr.loc,
                        cpt.LogicalNegate(operand.loc, operand),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Global):
                bounds: types.Interval = operand.interval
                # !G p = F !p
                expr.replace(
                    cpt.Future(
                        expr.loc,
                        cpt.LogicalNegate(operand.loc, operand),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Until):
                lhs: cpt.Expression = operand.get_lhs()
                rhs: cpt.Expression = operand.get_rhs()
                bounds: types.Interval = operand.interval
                # !(p U q) = !p R !q
                expr.replace(
                    cpt.Release(
                        expr.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Release):
                lhs: cpt.Expression = operand.get_lhs()
                rhs: cpt.Expression = operand.get_rhs()
                bounds: types.Interval = operand.interval
                # !(p R q) = !p U !q
                expr.replace(
                    cpt.Until(
                        expr.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    )
                )
        elif isinstance(expr, cpt.LogicalImplies):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p -> q = !p || q
            expr.replace(
                cpt.LogicalOr(expr.loc, [cpt.LogicalNegate(lhs.loc, lhs), rhs])
            )
        elif isinstance(expr, cpt.LogicalXor):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p xor q = (p && !q) || (!p && q)
            expr.replace(
                cpt.LogicalOr(
                    expr.loc,
                    [
                        cpt.LogicalAnd(
                            expr.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]
                        ),
                        cpt.LogicalAnd(
                            expr.loc, [cpt.LogicalNegate(lhs.loc, lhs), rhs]
                        ),
                    ],
                )
            )


def optimize_rewrite_rules(program: cpt.Program, context: cpt.Context) -> None:
    """Applies MLTL rewrite rules to reduce required SCQ memory."""
    return

    for expr in program.postorder(context):
        new: Optional[cpt.Expression] = None

        if isinstance(expr, cpt.LogicalNegate):
            opnd1 = expr.children[0]
            if isinstance(opnd1, cpt.Bool):
                if opnd1.value is True:
                    # !true = false
                    new = cpt.Bool(expr.loc, False)
                else:
                    # !false = true
                    new = cpt.Bool(expr.loc, True)
            elif isinstance(opnd1, cpt.LogicalNegate):
                # !!p = p
                new = opnd1.children[0]
            elif isinstance(opnd1, cpt.Global):
                opnd2 = opnd1.children[0]
                if isinstance(opnd2, cpt.LogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    new = cpt.Future(
                        expr.loc,
                        opnd2.children[0],
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                    )
            elif isinstance(opnd1, cpt.Future):
                opnd2 = opnd1.children[0]
                if isinstance(opnd2, cpt.LogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    new = cpt.Global(
                        expr.loc,
                        opnd2.children[0],
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                    )
        elif isinstance(expr, cpt.Equal):
            lhs = expr.children[0]
            rhs = expr.children[1]
            if isinstance(lhs, cpt.Bool) and isinstance(rhs, cpt.Bool):
                pass
            elif isinstance(lhs, cpt.Bool):
                # (true == p) = p
                new = rhs
            elif isinstance(rhs, cpt.Bool):
                # (p == true) = p
                new = lhs
        elif isinstance(expr, cpt.Global):
            opnd1 = expr.children[0]
            if expr.interval.lb == 0 and expr.interval.ub == 0:
                # G[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Bool):
                if opnd1.value is True:
                    # G[l,u]True = True
                    new = cpt.Bool(expr.loc, True)
                else:
                    # G[l,u]False = False
                    new = cpt.Bool(expr.loc, False)
            elif isinstance(opnd1, cpt.Global):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb: int = expr.interval.lb + opnd1.interval.lb
                ub: int = expr.interval.ub + opnd1.interval.ub
                new = cpt.Global(expr.loc, opnd2, lb, ub)
            elif isinstance(opnd1, cpt.Future):
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.Future(expr.loc, opnd2, lb, ub)
        elif isinstance(expr, cpt.Future):
            opnd1 = expr.children[0]
            if expr.interval.lb == 0 and expr.interval.ub == 0:
                # F[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Bool):
                if opnd1.value is True:
                    # F[l,u]True = True
                    new = cpt.Bool(expr.loc, True)
                else:
                    # F[l,u]False = False
                    new = cpt.Bool(expr.loc, False)
            elif isinstance(opnd1, cpt.Future):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb: int = expr.interval.lb + opnd1.interval.lb
                ub: int = expr.interval.ub + opnd1.interval.ub
                new = cpt.Future(expr.loc, opnd2, lb, ub)
            elif isinstance(opnd1, cpt.Global):
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.Global(expr.loc, opnd2, lb, ub)
        elif isinstance(expr, cpt.LogicalAnd):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if isinstance(lhs, cpt.Global) and isinstance(rhs, cpt.Global):
                p = lhs.children[0]
                q = rhs.children[0]
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q):  # check syntactic equivalence
                    # G[lb1,lb2]p && G[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.Global(expr.loc, p, lb1, ub1)
                        continue
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.Global(expr.loc, p, lb2, ub2)
                        continue
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.Global(expr.loc, p, lb1, max(ub1, ub2))
                        continue
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.Global(expr.loc, p, lb2, max(ub1, ub2))
                        continue

                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1 - lb1, ub2 - lb2)

                new = cpt.Global(
                    expr.loc,
                    cpt.LogicalAnd(
                        expr.loc,
                        [
                            cpt.Global(expr.loc, p, lb1 - lb3, ub1 - ub3),
                            cpt.Global(expr.loc, q, lb2 - lb3, ub2 - ub3),
                        ],
                    ),
                    lb3,
                    ub3,
                )
            elif isinstance(lhs, cpt.Future) and isinstance(rhs, cpt.Future):
                lhs_opnd = lhs.children[0]
                rhs_opnd = rhs.children[0]
                if str(lhs_opnd) == str(rhs_opnd):  # check for syntactic equivalence
                    # F[l1,u1]p && F[l2,u2]p = F[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and ub1 <= ub2:
                        # l2 <= l1 <= u1 <= u2
                        new = cpt.Future(expr.loc, lhs_opnd, lb1, ub1)
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = cpt.Future(expr.loc, lhs_opnd, lb2, ub2)
            elif isinstance(lhs, cpt.Until) and isinstance(rhs, cpt.Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    new = cpt.Until(
                        expr.loc,
                        cpt.LogicalAnd(expr.loc, [lhs_lhs, rhs_lhs]),
                        lhs_rhs,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                    )
        elif isinstance(expr, cpt.LogicalOr):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if isinstance(lhs, cpt.Future) and isinstance(rhs, cpt.Future):
                p = lhs.children[0]
                q = rhs.children[0]
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q):
                    # F[lb1,lb2]p || F[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.Future(expr.loc, p, lb1, ub1)
                        continue
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.Future(expr.loc, p, lb2, ub2)
                        continue
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.Future(expr.loc, p, lb1, max(ub1, ub2))
                        continue
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.Future(expr.loc, p, lb2, max(ub1, ub2))
                        continue

                # TODO: check for when lb==ub==0
                # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1 - lb1, ub2 - lb2)

                new = cpt.Future(
                    expr.loc,
                    cpt.LogicalOr(
                        expr.loc,
                        [
                            cpt.Future(expr.loc, p, lb1 - lb3, ub1 - ub3),
                            cpt.Future(expr.loc, q, lb2 - lb3, ub2 - ub3),
                        ],
                    ),
                    lb3,
                    ub3,
                )
            elif isinstance(lhs, cpt.Global) and isinstance(rhs, cpt.Global):
                lhs_opnd = lhs.children[0]
                rhs_opnd = rhs.children[0]
                if str(lhs_opnd) == str(rhs_opnd):
                    # G[l1,u1]p || G[l2,u2]p = G[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and ub1 <= ub2:
                        # l2 <= l1 <= u1 <= u2
                        new = cpt.Global(expr.loc, lhs_opnd, lb1, ub1)
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = cpt.Global(expr.loc, lhs_opnd, lb2, ub2)
            elif isinstance(lhs, cpt.Until) and isinstance(rhs, cpt.Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    new = cpt.Until(
                        expr.loc,
                        cpt.LogicalOr(expr.loc, [lhs_rhs, rhs_rhs]),
                        lhs_lhs,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                    )
        elif isinstance(expr, cpt.Until):
            lhs = expr.children[0]
            rhs = expr.children[1]
            if (
                isinstance(rhs, cpt.Global)
                and rhs.interval.lb == 0
                and str(lhs) == str(rhs.children[0])
            ):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                new = cpt.Global(
                    expr.loc, lhs, expr.interval.lb, expr.interval.lb + rhs.interval.ub
                )
            elif (
                isinstance(rhs, cpt.Future)
                and rhs.interval.lb == 0
                and str(lhs) == str(rhs.children[0])
            ):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                new = cpt.Future(
                    expr.loc, lhs, expr.interval.lb, expr.interval.lb + rhs.interval.ub
                )

        if new:
            log.debug(
                f"\n\t{expr}\n\t\t===>\n\t{new}", module=MODULE_CODE, submodule="RWR"
            )
            expr.replace(new)


def optimize_cse(program: cpt.Program, context: cpt.Context) -> None:
    """Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence. Applies CSE to FT/PT formulas separately."""
    return

    S: dict[str, cpt.Expression]

    log.debug("Performing CSE", module=MODULE_CODE, submodule="CSE")

    def _optimize_cse(expr: cpt.Expression) -> None:
        nonlocal S

        if str(expr) in S:
            log.debug(f"Replacing --- {expr}", module=MODULE_CODE, submodule="CSE")
            expr.replace(S[str(expr)])
        else:
            log.debug(f"Visiting ---- {expr}", module=MODULE_CODE, submodule="CSE")
            S[str(expr)] = expr

    S = {}
    for expr in cpt.postorder(program.ft_spec_set, context):
        _optimize_cse(expr)

    S = {}
    for expr in cpt.postorder(program.pt_spec_set, context):
        _optimize_cse(expr)


def compute_atomics(program: cpt.Program, context: cpt.Context) -> None:
    """Compute atomics and store them in `context`. An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine."""
    id: int = 0

    for expr in program.postorder(context):
        if expr.engine == types.R2U2Engine.TEMPORAL_LOGIC:
            continue

        if isinstance(expr, cpt.Bool):
            continue

        for parent in [p for p in expr.parents if isinstance(p, cpt.Expression)]:
            if parent.engine == types.R2U2Engine.TEMPORAL_LOGIC:
                context.atomics.add(expr)
                if expr.atomic_id < 0:
                    expr.atomic_id = id
                    id += 1

    log.debug(
        f"Computed atomics:\n\t[{', '.join(f'({a},{a.atomic_id})' for a in context.atomics)}]",
        module=MODULE_CODE,
        submodule="ATM",
    )


def compute_scq_sizes(program: cpt.Program, context: cpt.Context) -> None:
    """Computes SCQ sizes for each node."""
    spec_section_total_scq_size = 0

    for expr in cpt.postorder(program.ft_spec_set, context):
        if isinstance(expr, cpt.SpecSection):
            expr.total_scq_size = spec_section_total_scq_size
            spec_section_total_scq_size = 0
            continue

        if isinstance(expr, cpt.Formula):
            expr.scq_size = 1
            expr.total_scq_size = expr.get_expr().total_scq_size + expr.scq_size
            spec_section_total_scq_size += expr.scq_size
            expr.scq = (
                spec_section_total_scq_size - expr.scq_size,
                spec_section_total_scq_size,
            )
            continue

        if (
            expr.engine != types.R2U2Engine.TEMPORAL_LOGIC
            and expr not in context.atomics
        ):
            continue

        max_wpd = max([sibling.wpd for sibling in expr.get_siblings()] + [0])

        # need the +3 b/c of implementation -- ask Brian
        expr.scq_size = max(max_wpd - expr.bpd, 0) + 3
        expr.total_scq_size = (
            sum([c.total_scq_size for c in expr.children if c.scq_size > -1])
            + expr.scq_size
        )
        spec_section_total_scq_size += expr.scq_size

        expr.scq = (
            spec_section_total_scq_size - expr.scq_size,
            spec_section_total_scq_size,
        )


def optimize_egraph(program: cpt.Program, context: cpt.Context):
    pass


# A ast.C2POTransform is a function with the signature:
#    transform(program, context) -> None
C2POTransform = Callable[[cpt.Program, cpt.Context], None]

# This is ORDER-SENSITIVE
TRANSFORM_PIPELINE: list[C2POTransform] = [
    transform_definitions,
    transform_function_calls,
    transform_contracts,
    transform_set_aggregation,
    transform_struct_accesses,
    optimize_rewrite_rules,
    transform_extended_operators,
    transform_negative_normal_form,
    transform_boolean_normal_form,
    optimize_cse,
    compute_atomics,  # not a transform, but needed for assembly+analysis
    optimize_egraph,
    compute_scq_sizes,  # not a transform, but needed for assembly+analysis
]
