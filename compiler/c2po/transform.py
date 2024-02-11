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

    log.debug(f"Post definition expansion:\n{repr(program)}", MODULE_CODE)


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
                cpt.Operator.LogicalImplies(
                    contract.loc, contract.get_assumption(), contract.get_guarantee()
                ),
            ),
            cpt.Formula(
                contract.loc,
                f"__{contract.symbol}_verified__",
                contract.formula_numbers[2],
                cpt.Operator.LogicalAnd(
                    contract.loc, [contract.get_assumption(), contract.get_guarantee()]
                ),
            ),
        ]

        new_formulas = cast("list[cpt.Specification]", new_formulas)

        program.replace_spec(contract, new_formulas)

        log.debug(f"Replaced contract '{contract.symbol}'", MODULE_CODE)

    log.debug(f"Post contract replacement:\n{repr(program)}", MODULE_CODE)


def transform_set_aggregation(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction."""
    log.debug("Unrolling set aggregation expressions.", MODULE_CODE)

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
        if type(expr) is not cpt.SetAggregation:
            continue

        if expr.operator is cpt.SetAggregationType.FOR_EACH:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.LogicalAnd(
                expr.loc,
                [
                    cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                    for e in expr.get_set().children
                ],
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationType.FOR_SOME:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.LogicalOr(
                expr.loc,
                [
                    cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                    for e in expr.get_set().children
                ],
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationType.FOR_EXACTLY:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.Equal(
                expr.loc,
                cpt.Operator.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                    types.IntType()
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationType.FOR_AT_LEAST:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.GreaterThanOrEqual(
                expr.loc,
                cpt.Operator.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                    types.IntType()
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationType.FOR_AT_MOST:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.LessThanOrEqual(
                expr.loc,
                cpt.Operator.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                    types.IntType()
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)

    log.debug(f"Post set aggregation unrolling:\n{repr(program)}", MODULE_CODE)


def transform_struct_accesses(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms struct access operations to the underlying member expression."""
    log.debug("Resolving struct accesses.", MODULE_CODE)

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.StructAccess):
            continue

        s: cpt.Struct = expr.get_struct()
        member = s.get_member(expr.member)
        if member:
            expr.replace(member)

    log.debug(f"Post struct access resolution:\n{repr(program)}", MODULE_CODE)


def transform_extended_operators(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms specifications in `program` to remove extended operators (or, xor, implies, iff, release, future)."""
    log.debug("Removing extended operators.", MODULE_CODE)

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.Operator):
            continue

        if expr.operator is cpt.OperatorKind.LOGICAL_OR:
            # p || q = !(!p && !q)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.Operator.LogicalAnd(
                        expr.loc,
                        [cpt.Operator.LogicalNegate(c.loc, c) for c in expr.children],
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.LOGICAL_XOR:
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p xor q = (p && !q) || (!p && q) = !(!(p && !q) && !(!p && q))
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.Operator.LogicalAnd(
                        expr.loc,
                        [
                            cpt.Operator.LogicalNegate(
                                expr.loc,
                                cpt.Operator.LogicalAnd(
                                    expr.loc,
                                    [lhs, cpt.Operator.LogicalNegate(rhs.loc, rhs)],
                                ),
                            ),
                            cpt.Operator.LogicalNegate(
                                expr.loc,
                                cpt.Operator.LogicalAnd(
                                    expr.loc,
                                    [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs],
                                ),
                            ),
                        ],
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.LOGICAL_IMPLIES:
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p -> q = !(p && !q)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.Operator.LogicalAnd(
                        lhs.loc, [lhs, cpt.Operator.LogicalNegate(rhs.loc, rhs)]
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.LOGICAL_IFF:
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p <-> q = !(p && !q) && !(p && !q)
            expr.replace(
                cpt.Operator.LogicalAnd(
                    expr.loc,
                    [
                        cpt.Operator.LogicalNegate(
                            expr.loc,
                            cpt.Operator.LogicalAnd(
                                lhs.loc, [lhs, cpt.Operator.LogicalNegate(rhs.loc, rhs)]
                            ),
                        ),
                        cpt.Operator.LogicalNegate(
                            expr.loc,
                            cpt.Operator.LogicalAnd(
                                lhs.loc, [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs]
                            ),
                        ),
                    ],
                )
            )
        elif expr.operator is cpt.OperatorKind.RELEASE:
            expr = cast(cpt.TemporalOperator, expr)

            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            interval = expr.interval
            # p R q = !(!p U !q)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.TemporalOperator.Until(
                        expr.loc,
                        interval.lb,
                        interval.ub,
                        cpt.Operator.LogicalNegate(lhs.loc, lhs),
                        cpt.Operator.LogicalNegate(rhs.loc, rhs),
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.FUTURE:
            expr = cast(cpt.TemporalOperator, expr)

            operand: cpt.Expression = expr.children[0]

            interval = expr.interval
            # F p = True U p
            expr.replace(
                cpt.TemporalOperator.Until(
                    expr.loc,
                    interval.lb,
                    interval.ub,
                    cpt.Constant(expr.loc, True),
                    operand,
                )
            )

    log.debug(f"Post extended operator removal:\n{repr(program)}", MODULE_CODE)


def transform_boolean_normal_form(program: cpt.Program, context: cpt.Context) -> None:
    """Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators."""

    for expr in program.postorder(context):
        if type(expr) is not cpt.Operator:
            continue

        if expr.operator is cpt.OperatorKind.LOGICAL_OR:
            # p || q = !(!p && !q)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.Operator.LogicalAnd(
                        expr.loc,
                        [cpt.Operator.LogicalNegate(c.loc, c) for c in expr.children],
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.LOGICAL_IMPLIES:
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p -> q = !(p && !q)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.Operator.LogicalAnd(
                        expr.loc, [lhs, cpt.Operator.LogicalNegate(rhs.loc, rhs)]
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.LOGICAL_XOR:
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p xor q = !(!p && !q) && !(p && q)
            expr.replace(
                cpt.Operator.LogicalAnd(
                    expr.loc,
                    [
                        cpt.Operator.LogicalNegate(
                            expr.loc,
                            cpt.Operator.LogicalAnd(
                                lhs.loc,
                                [
                                    cpt.Operator.LogicalNegate(lhs.loc, lhs),
                                    cpt.Operator.LogicalNegate(rhs.loc, rhs),
                                ],
                            ),
                        ),
                        cpt.Operator.LogicalNegate(
                            lhs.loc, cpt.Operator.LogicalAnd(lhs.loc, [lhs, rhs])
                        ),
                    ],
                )
            )
        elif expr.operator is cpt.OperatorKind.FUTURE:
            expr = cast(cpt.TemporalOperator, expr)
            operand: cpt.Expression = expr.children[0]
            bounds: types.Interval = expr.interval
            # F p = True U p
            expr.replace(
                cpt.TemporalOperator.Until(
                    expr.loc,
                    bounds.lb,
                    bounds.ub,
                    cpt.Constant(operand.loc, True),
                    operand,
                )
            )
        elif expr.operator is cpt.OperatorKind.GLOBAL:
            expr = cast(cpt.TemporalOperator, expr)
            operand: cpt.Expression = expr.children[0]
            bounds: types.Interval = expr.interval
            # G p = !(True U !p)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.TemporalOperator.Until(
                        expr.loc,
                        bounds.lb,
                        bounds.ub,
                        cpt.Constant(operand.loc, True),
                        cpt.Operator.LogicalNegate(operand.loc, operand),
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.RELEASE:
            expr = cast(cpt.TemporalOperator, expr)
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            bounds: types.Interval = expr.interval
            # p R q = !(!p U !q)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.TemporalOperator.Until(
                        expr.loc,
                        bounds.lb,
                        bounds.ub,
                        cpt.Operator.LogicalNegate(lhs.loc, lhs),
                        cpt.Operator.LogicalNegate(rhs.loc, rhs),
                    ),
                )
            )


def transform_negative_normal_form(program: cpt.Program, context: cpt.Context) -> None:
    """FIXME: currently does not work properly

    Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals."""
    return

    for expr in program.postorder(context):
        if type(expr) is not cpt.Operator:
            continue

        if isinstance(expr, cpt.Operator.LogicalNegate):
            operand = expr.children[0]
            if isinstance(operand, cpt.Operator.LogicalNegate):
                # !!p = p
                expr.replace(operand.children[0])
            if isinstance(operand, cpt.Operator.LogicalOr):
                # !(p || q) = !p && !q
                expr.replace(
                    cpt.Operator.LogicalAnd(
                        expr.loc,
                        [
                            cpt.Operator.LogicalNegate(c.loc, c)
                            for c in operand.children
                        ],
                    )
                )
            if isinstance(operand, cpt.Operator.LogicalAnd):
                # !(p && q) = !p || !q
                expr.replace(
                    cpt.Operator.LogicalOr(
                        expr.loc,
                        [
                            cpt.Operator.LogicalNegate(c.loc, c)
                            for c in operand.children
                        ],
                    )
                )
            elif isinstance(operand, cpt.Future):
                bounds: types.Interval = operand.interval
                # !F p = G !p
                expr.replace(
                    cpt.Global(
                        expr.loc,
                        cpt.Operator.LogicalNegate(operand.loc, operand),
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
                        cpt.Operator.LogicalNegate(operand.loc, operand),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Until):
                lhs: cpt.Expression = operand.children[0]
                rhs: cpt.Expression = operand.children[1]
                bounds: types.Interval = operand.interval
                # !(p U q) = !p R !q
                expr.replace(
                    cpt.Release(
                        expr.loc,
                        cpt.Operator.LogicalNegate(lhs.loc, lhs),
                        cpt.Operator.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Release):
                lhs: cpt.Expression = operand.children[0]
                rhs: cpt.Expression = operand.children[1]
                bounds: types.Interval = operand.interval
                # !(p R q) = !p U !q
                expr.replace(
                    cpt.Until(
                        expr.loc,
                        cpt.Operator.LogicalNegate(lhs.loc, lhs),
                        cpt.Operator.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    )
                )
        elif isinstance(expr, cpt.Operator.LogicalImplies):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p -> q = !p || q
            expr.replace(
                cpt.Operator.LogicalOr(
                    expr.loc, [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs]
                )
            )
        elif isinstance(expr, cpt.Operator.LogicalXor):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p xor q = (p && !q) || (!p && q)
            expr.replace(
                cpt.Operator.LogicalOr(
                    expr.loc,
                    [
                        cpt.Operator.LogicalAnd(
                            expr.loc, [lhs, cpt.Operator.LogicalNegate(rhs.loc, rhs)]
                        ),
                        cpt.Operator.LogicalAnd(
                            expr.loc, [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs]
                        ),
                    ],
                )
            )


def optimize_rewrite_rules(program: cpt.Program, context: cpt.Context) -> None:
    """Applies MLTL rewrite rules to reduce required SCQ memory."""
    return

    for expr in program.postorder(context):
        new: Optional[cpt.Expression] = None

        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            opnd1 = expr.children[0]
            if type(opnd1) is cpt.Constant:
                if opnd1.value is True:
                    # !true = false
                    new = cpt.Constant(expr.loc, False)
                else:
                    # !false = true
                    new = cpt.Constant(expr.loc, True)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.LOGICAL_NEGATE):
                # !!p = p
                new = opnd1.children[0]
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                opnd2 = opnd1.children[0]
                if cpt.is_operator(opnd2, cpt.OperatorKind.LOGICAL_NEGATE):
                    # !(G[l,u](!p)) = F[l,u]p
                    new = cpt.Operator.Future(
                        expr.loc,
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                        opnd2.children[0],
                    )
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd2 = opnd1.children[0]
                if cpt.is_operator(opnd2, cpt.OperatorKind.LOGICAL_NEGATE):
                    # !(F[l,u](!p)) = G[l,u]p
                    new = cpt.Operator.Global(
                        expr.loc,
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                        opnd2.children[0],
                    )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            lhs = expr.children[0]
            rhs = expr.children[1]
            if type(lhs) is cpt.Constant and type(rhs) is cpt.Constant:
                pass
            elif type(lhs) is cpt.Constant:
                # (true == p) = p
                new = rhs
            elif type(rhs) is cpt.Constant:
                # (p == true) = p
                new = lhs
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            opnd1 = expr.children[0]
            if expr.interval.lb == 0 and expr.interval.ub == 0:
                # G[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Constant):
                if opnd1.value is True:
                    # G[l,u]True = True
                    new = cpt.Constant(expr.loc, True)
                else:
                    # G[l,u]False = False
                    new = cpt.Constant(expr.loc, False)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb: int = expr.interval.lb + opnd1.interval.lb
                ub: int = expr.interval.ub + opnd1.interval.ub
                new = cpt.Global(expr.loc, opnd2, lb, ub)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.Future(expr.loc, opnd2, lb, ub)
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            opnd1 = expr.children[0]
            if expr.interval.lb == 0 and expr.interval.ub == 0:
                # F[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Constant):
                if opnd1.value is True:
                    # F[l,u]True = True
                    new = cpt.Constant(expr.loc, True)
                else:
                    # F[l,u]False = False
                    new = cpt.Constant(expr.loc, False)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb: int = expr.interval.lb + opnd1.interval.lb
                ub: int = expr.interval.ub + opnd1.interval.ub
                new = cpt.Future(expr.loc, opnd2, lb, ub)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.Global(expr.loc, opnd2, lb, ub)
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if cpt.is_operator(lhs, cpt.OperatorKind.GLOBAL) and cpt.is_operator(
                rhs, cpt.OperatorKind.GLOBAL
            ):
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
                    cpt.Operator.LogicalAnd(
                        expr.loc,
                        [
                            cpt.Global(expr.loc, p, lb1 - lb3, ub1 - ub3),
                            cpt.Global(expr.loc, q, lb2 - lb3, ub2 - ub3),
                        ],
                    ),
                    lb3,
                    ub3,
                )
            elif cpt.is_operator(lhs, cpt.OperatorKind.FUTURE) and cpt.is_operator(
                rhs, cpt.OperatorKind.FUTURE
            ):
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
            elif cpt.is_operator(lhs, cpt.OperatorKind.UNTIL) and cpt.is_operator(
                rhs, cpt.OperatorKind.UNTIL
            ):
                lhs_lhs = lhs.children[0]
                lhs_rhs = lhs.children[1]
                rhs_lhs = rhs.children[0]
                rhs_rhs = rhs.children[1]
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    new = cpt.Until(
                        expr.loc,
                        cpt.Operator.LogicalAnd(expr.loc, [lhs_lhs, rhs_lhs]),
                        lhs_rhs,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                    )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if cpt.is_operator(lhs, cpt.OperatorKind.FUTURE) and cpt.is_operator(
                rhs, cpt.OperatorKind.FUTURE
            ):
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
                    cpt.Operator.LogicalOr(
                        expr.loc,
                        [
                            cpt.Future(expr.loc, p, lb1 - lb3, ub1 - ub3),
                            cpt.Future(expr.loc, q, lb2 - lb3, ub2 - ub3),
                        ],
                    ),
                    lb3,
                    ub3,
                )
            elif cpt.is_operator(lhs, cpt.OperatorKind.GLOBAL) and cpt.is_operator(
                rhs, cpt.OperatorKind.GLOBAL
            ):
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
            elif cpt.is_operator(lhs, cpt.OperatorKind.UNTIL) and cpt.is_operator(
                rhs, cpt.OperatorKind.UNTIL
            ):
                lhs_lhs = lhs.children[0]
                lhs_rhs = lhs.children[1]
                rhs_lhs = rhs.children[0]
                rhs_rhs = rhs.children[1]
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    new = cpt.Until(
                        expr.loc,
                        cpt.Operator.LogicalOr(expr.loc, [lhs_rhs, rhs_rhs]),
                        lhs_lhs,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                    )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
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
    S: dict[str, cpt.Expression]

    log.debug("Performing CSE", module=MODULE_CODE)

    def _optimize_cse(expr: cpt.Expression) -> None:
        nonlocal S

        if str(expr) in S:
            log.debug(f"Replacing --- {expr}", module=MODULE_CODE)
            expr.replace(S[str(expr)])
        else:
            log.debug(f"Visiting ---- {expr}", module=MODULE_CODE)
            S[str(expr)] = expr

    S = {}
    for expr in cpt.postorder(program.ft_spec_set, context):
        _optimize_cse(expr)

    S = {}
    for expr in cpt.postorder(program.pt_spec_set, context):
        _optimize_cse(expr)

    log.debug(f"Post CSE:\n{repr(program)}", MODULE_CODE)


def transform_multi_operator(program: cpt.Program, context: cpt.Context) -> None:
    """Converts all multi-arity operators (e.g., &&, ||, +) to binary."""
    log.debug("Converting multi-arity operators", module=MODULE_CODE)

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.Operator) or len(expr.children) < 3:
            continue

        if expr.operator in {
            cpt.OperatorKind.LOGICAL_AND,
            cpt.OperatorKind.LOGICAL_OR,
            cpt.OperatorKind.ARITHMETIC_ADD,
            cpt.OperatorKind.ARITHMETIC_MULTPLY,
        }:
            new = type(expr)(expr.loc, expr.operator, expr.children[0:2], expr.type)
            for i in range(2, len(expr.children) - 1):
                new = type(expr)(expr.loc, expr.operator, [new, expr.children[i]], expr.type)
            new = type(expr)(expr.loc, expr.operator, [new, expr.children[-1]], expr.type)

            expr.replace(new)

    log.debug(f"Post multi-arity operator conversion:\n{repr(program)}", MODULE_CODE)


def compute_atomics(program: cpt.Program, context: cpt.Context) -> None:
    """Compute atomics and store them in `context`. An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine."""
    id: int = 0

    for expr in program.postorder(context):
        if expr.engine == types.R2U2Engine.TEMPORAL_LOGIC:
            continue

        if isinstance(expr, cpt.Constant):
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
    transform_multi_operator,
    compute_atomics,  # not a transform, but needed for assembly+analysis
    compute_scq_sizes,  # not a transform, but needed for assembly+analysis
]
