from __future__ import annotations
from copy import deepcopy
from typing import Callable, Optional, cast

from c2po import cpt, log, types, sat, eqsat, options

MODULE_CODE = "PASS"


def expand_definitions(program: cpt.Program, context: cpt.Context) -> None:
    """Expands each definition symbol in the definitions and specifications of `program` to its expanded definition. This is essentially macro expansion."""
    log.debug(MODULE_CODE, 1, "Expanding definitions")

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

    log.debug(MODULE_CODE, 1, f"Post definition expansion:\n{repr(program)}")


def convert_function_calls_to_structs(program: cpt.Program, context: cpt.Context) -> None:
    """Converts each function call in `program` that corresponds to a struct instantiation to a `cpt.Struct`."""
    log.debug(MODULE_CODE, 1, "Converting function calls to structs")
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


def resolve_contracts(program: cpt.Program, context: cpt.Context) -> None:
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""
    log.debug(MODULE_CODE, 1, "Replacing contracts")

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

        for formula in new_formulas:
            formula.get_expr().type = types.BoolType()

        new_formulas = cast("list[cpt.Specification]", new_formulas)

        program.replace_spec(contract, new_formulas)

        log.debug(MODULE_CODE, 1, f"Replaced contract '{contract.symbol}'")

    log.debug(MODULE_CODE, 1, f"Post contract replacement:\n{repr(program)}")


def unroll_set_aggregation(program: cpt.Program, context: cpt.Context) -> None:
    """Unrolls set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction."""
    log.debug(MODULE_CODE, 1, "Unrolling set aggregation expressions.")

    def resolve_struct_accesses(expr: cpt.Expression, context: cpt.Context) -> None:
        if not isinstance(expr, cpt.StructAccess):
            return

        s = expr.get_struct()
        if not isinstance(s, cpt.Struct):
            return

        member = s.get_member(expr.member)
        if not member:
            raise ValueError(f"Member {expr.member} not found in struct {s} --- issue with type checking\n"
                             f"Please open an issue at {log.ISSUE_URL}.")

        new_type = member.type
        if member:
            expr.replace(member)
            member.type = new_type

    for expr in program.preorder(context):
        if not isinstance(expr, cpt.SetAggregation):
            continue

        if expr.operator is cpt.SetAggregationKind.FOR_EACH:
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
        elif expr.operator is cpt.SetAggregationKind.FOR_SOME:
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
        elif expr.operator is cpt.SetAggregationKind.FOR_EXACTLY:
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
                    types.IntType(),
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationKind.FOR_AT_LEAST:
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
                    types.IntType(),
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationKind.FOR_AT_MOST:
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
                    types.IntType(),
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)

    log.debug(MODULE_CODE, 1, f"Post set aggregation unrolling:\n{repr(program)}")


def resolve_struct_accesses(program: cpt.Program, context: cpt.Context) -> None:
    """Resolves struct access operations to the underlying member expression."""
    log.debug(MODULE_CODE, 1, "Resolving struct accesses.")

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.StructAccess):
            continue

        s = expr.get_struct()
        if not isinstance(s, cpt.Struct):
            continue

        member = s.get_member(expr.member)
        if not member:
            raise ValueError(f"Member {expr.member} not found in struct {s} --- issue with type checking\n"
                             f"Please open an issue at {log.ISSUE_URL}.")

        new_type = member.type
        if member:
            expr.replace(member)
            member.type = new_type

    log.debug(MODULE_CODE, 1, f"Post struct access resolution:\n{repr(program)}")


def resolve_array_accesses(program: cpt.Program, context: cpt.Context) -> None:
    """Resolves array access operations to the underlying member expression."""
    log.debug(MODULE_CODE, 1, "Resolving array accesses.")

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.ArrayIndex):
            continue

        # Not all out-of-bounds errors are checked during type checking
        # Ex: a struct has an array member type of uninterpreted size,
        # must check this case here
        array_type = cast(types.ArrayType, expr.get_array().type)
        if expr.get_index() >= array_type.size:
            log.error(MODULE_CODE, f"Out-of-bounds array index ({expr})", expr.loc)
            context.status = False
            continue

        array = expr.get_array()
        expr.replace(array.children[expr.get_index()])

    log.debug(MODULE_CODE, 1, f"Post array access resolution:\n{repr(program)}")


def remove_extended_operators(program: cpt.Program, context: cpt.Context) -> None:
    """Removes extended operators (Global, Future, Historically, Once, xor, implies) from each specification in `program`."""
    log.debug(MODULE_CODE, 1, "Removing extended operators.")

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.Operator):
            continue

        if expr.operator is cpt.OperatorKind.LOGICAL_XOR:
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p xor q = !(p <-> q)
            expr.replace(
                cpt.Operator.LogicalNegate(
                    expr.loc,
                    cpt.Operator.LogicalIff(
                        expr.loc,
                        lhs, 
                        rhs,
                    ),
                )
            )
        elif expr.operator is cpt.OperatorKind.LOGICAL_IMPLIES:
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]
            # p -> q = !p || q)
            expr.replace(
                cpt.Operator.LogicalOr(
                    expr.loc, [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs]
                ),
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
        elif expr.operator is cpt.OperatorKind.GLOBAL:
            expr = cast(cpt.TemporalOperator, expr)

            operand: cpt.Expression = expr.children[0]

            interval = expr.interval
            # G p = False R p
            expr.replace(
                cpt.TemporalOperator.Release(
                    expr.loc,
                    interval.lb,
                    interval.ub,
                    cpt.Constant(expr.loc, False),
                    operand,
                )
            )
        elif expr.operator is cpt.OperatorKind.ONCE:
            expr = cast(cpt.TemporalOperator, expr)

            operand: cpt.Expression = expr.children[0]

            interval = expr.interval
            # O p = True S p
            expr.replace(
                cpt.TemporalOperator.Since(
                    expr.loc,
                    interval.lb,
                    interval.ub,
                    cpt.Constant(expr.loc, True),
                    operand,
                )
            )
        elif expr.operator is cpt.OperatorKind.HISTORICAL:
            expr = cast(cpt.TemporalOperator, expr)

            operand: cpt.Expression = expr.children[0]

            interval = expr.interval
            # H p = False T p
            expr.replace(
                cpt.TemporalOperator.Trigger(
                    expr.loc,
                    interval.lb,
                    interval.ub,
                    cpt.Constant(expr.loc, False),
                    operand,
                )
            )

    log.debug(MODULE_CODE, 1, f"Post extended operator removal:\n{repr(program)}")


def to_bnf(program: cpt.Program, context: cpt.Context) -> None:
    """Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators."""
    log.debug(MODULE_CODE, 1, "Converting to BNF")

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

    log.debug(MODULE_CODE, 1, f"Post BNF conversion:\n{repr(program)}")


def to_nnf(program: cpt.Program, context: cpt.Context) -> None:
    """Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals."""
    log.debug(MODULE_CODE, 1, "Converting to NNF")

    for expr in program.preorder(context):
        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            operand = expr.children[0]

            if cpt.is_operator(operand, cpt.OperatorKind.LOGICAL_NEGATE):
                # !!p |-> p
                expr.replace(operand.children[0])
            elif cpt.is_operator(operand, cpt.OperatorKind.LOGICAL_OR):
                # !(p || q) |-> !p && !q
                expr.replace(
                    cpt.Operator.LogicalAnd(
                        expr.loc,
                        [
                            cpt.Operator.LogicalNegate(c.loc, c)
                            for c in operand.children
                        ],
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.LOGICAL_AND):
                # !(p && q) |-> !p || !q
                expr.replace(
                    cpt.Operator.LogicalOr(
                        expr.loc,
                        [
                            cpt.Operator.LogicalNegate(c.loc, c)
                            for c in operand.children
                        ],
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.LOGICAL_IMPLIES):
                lhs: cpt.Expression = operand.children[0]
                rhs: cpt.Expression = operand.children[1]

                # ! (p -> q) |-> ! (!p || q) |-> p && !q
                expr.replace(
                    cpt.Operator.LogicalAnd(
                        expr.loc, [lhs, cpt.Operator.LogicalNegate(lhs.loc, rhs)]
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.LOGICAL_XOR):
                lhs: cpt.Expression = operand.children[0]
                rhs: cpt.Expression = operand.children[1]
                
                # ! (p xor q) |-> ! ((p && !q) || (!p && q)) |-> !(p && !q) && ! (!p && q) |-> (!p || q) && (p || !q)
                expr.replace(
                    cpt.Operator.LogicalAnd(
                        expr.loc,
                        [
                            cpt.Operator.LogicalAnd(
                                expr.loc, [cpt.Operator.LogicalNegate(rhs.loc, lhs), rhs]
                            ),
                            cpt.Operator.LogicalAnd(
                                expr.loc, [lhs, cpt.Operator.LogicalNegate(lhs.loc, rhs)]
                            ),
                        ],
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.LOGICAL_EQUIV):
                lhs: cpt.Expression = operand.children[0]
                rhs: cpt.Expression = operand.children[1]
                
                # ! (p <-> q) |-> ! ((p -> q) && (q -> p)) |-> !(p -> q) || !(q -> p) |-> (p && !q) || (q && !p)
                expr.replace(
                    cpt.Operator.LogicalOr(
                        expr.loc,
                        [
                            cpt.Operator.LogicalAnd(
                                expr.loc, [lhs, cpt.Operator.LogicalNegate(rhs.loc, rhs)]
                            ),
                            cpt.Operator.LogicalAnd(
                                expr.loc, [cpt.Operator.LogicalNegate(rhs.loc, lhs), rhs]
                            ),
                        ],
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.FUTURE):
                operand = cast(cpt.TemporalOperator, operand)
                bounds: types.Interval = operand.interval

                # !F p = G !p
                expr.replace(
                    cpt.TemporalOperator.Global(
                        expr.loc,
                        bounds.lb,
                        bounds.ub,
                        cpt.Operator.LogicalNegate(operand.loc, operand.children[0]),
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.GLOBAL):
                operand = cast(cpt.TemporalOperator, operand)
                bounds: types.Interval = operand.interval

                # !G p = F !p
                expr.replace(
                    cpt.TemporalOperator.Future(
                        expr.loc,
                        bounds.lb,
                        bounds.ub,
                        cpt.Operator.LogicalNegate(operand.loc, operand.children[0]),
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.UNTIL):
                operand = cast(cpt.TemporalOperator, operand)

                lhs: cpt.Expression = operand.children[0]
                rhs: cpt.Expression = operand.children[1]
                
                bounds: types.Interval = operand.interval

                # !(p U q) = !p R !q
                expr.replace(
                    cpt.TemporalOperator.Release(
                        expr.loc,
                        bounds.lb,
                        bounds.ub,
                        cpt.Operator.LogicalNegate(lhs.loc, lhs),
                        cpt.Operator.LogicalNegate(rhs.loc, rhs),
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.RELEASE):
                operand = cast(cpt.TemporalOperator, operand)

                lhs: cpt.Expression = operand.children[0]
                rhs: cpt.Expression = operand.children[1]

                bounds: types.Interval = operand.interval

                # !(p R q) = !p U !q
                expr.replace(
                    cpt.TemporalOperator.Until(
                        expr.loc,
                        bounds.lb,
                        bounds.ub,
                        cpt.Operator.LogicalNegate(lhs.loc, lhs),
                        cpt.Operator.LogicalNegate(rhs.loc, rhs),
                    )
                )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]

            # p -> q = !p || q
            expr.replace(
                cpt.Operator.LogicalOr(
                    expr.loc, [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs]
                )
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_XOR):
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

    log.debug(MODULE_CODE, 1, f"Post NNF conversion:\n{repr(program)}")


def optimize_rewrite_rules(program: cpt.Program, context: cpt.Context) -> None:
    """Applies MLTL rewrite rules to reduce required SCQ memory."""
    log.debug(MODULE_CODE, 1, "Performing rewrites")

    for expr in program.postorder(context):
        new: Optional[cpt.Expression] = None

        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            opnd1 = expr.children[0]
            if isinstance(opnd1, cpt.Constant):
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
                opnd1 = cast(cpt.TemporalOperator, opnd1)

                opnd2 = opnd1.children[0]
                if cpt.is_operator(opnd2, cpt.OperatorKind.LOGICAL_NEGATE):
                    # !(G[l,u](!p)) = F[l,u]p
                    new = cpt.TemporalOperator.Future(
                        expr.loc,
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                        opnd2.children[0],
                    )
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd1 = cast(cpt.TemporalOperator, opnd1)

                opnd2 = opnd1.children[0]
                if cpt.is_operator(opnd2, cpt.OperatorKind.LOGICAL_NEGATE):
                    # !(F[l,u](!p)) = G[l,u]p
                    new = cpt.TemporalOperator.Global(
                        expr.loc,
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                        opnd2.children[0],
                    )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            lhs = expr.children[0]
            rhs = expr.children[1]
            if isinstance(lhs, cpt.Constant) and isinstance(rhs, cpt.Constant):
                pass
            elif isinstance(lhs, cpt.Constant) and isinstance(lhs.value, bool):
                # (true == p) = p
                new = rhs
            elif isinstance(rhs, cpt.Constant) and isinstance(rhs.value, bool):
                # (p == true) = p
                new = lhs
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)

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
                    # erroneous: the empty trace satisfies "G[l,u] False", but not "False"
                    # new = cpt.Constant(expr.loc, False)
                    pass
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb: int = expr.interval.lb + opnd1.interval.lb
                ub: int = expr.interval.ub + opnd1.interval.ub
                new = cpt.TemporalOperator.Global(expr.loc, lb, ub, opnd2)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Future(expr.loc, lb, ub, opnd2)
                elif opnd1.interval.lb == opnd1.interval.ub:
                    # G[l,u](F[a,a]p) = G[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Global(expr.loc, lb, ub, opnd2)
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)

            opnd1 = expr.children[0]
            if expr.interval.lb == 0 and expr.interval.ub == 0:
                # F[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Constant):
                if opnd1.value is True:
                    # F[l,u]True = True
                    # erroneous: the empty trace satisfies "True", but not "F[l,u] True"
                    # new = cpt.Constant(expr.loc, True)
                    pass
                else:
                    # F[l,u]False = False
                    new = cpt.Constant(expr.loc, False)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb: int = expr.interval.lb + opnd1.interval.lb
                ub: int = expr.interval.ub + opnd1.interval.ub
                new = cpt.TemporalOperator.Future(expr.loc, lb, ub, opnd2)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Global(expr.loc, lb, ub, opnd2)
                elif opnd1.interval.lb == opnd1.interval.ub:
                    # F[l,u](G[a,a]p) = F[l+a,u+a]p
                    lb: int = expr.interval.lb + opnd1.interval.lb
                    ub: int = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Future(expr.loc, lb, ub, opnd2)
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if (
                cpt.is_operator(lhs, cpt.OperatorKind.GLOBAL) and 
                cpt.is_operator(rhs, cpt.OperatorKind.GLOBAL)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

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
                        new = cpt.TemporalOperator.Global(expr.loc, lb1, ub1, p)
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.TemporalOperator.Global(expr.loc,lb2, ub2, p)
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.TemporalOperator.Global(expr.loc, lb1, max(ub1, ub2), p)
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.TemporalOperator.Global(expr.loc, lb2, max(ub1, ub2), p)
                else:
                    lb3: int = min(lb1, lb2)
                    ub3: int = lb3 + min(ub1 - lb1, ub2 - lb2)

                    new = cpt.TemporalOperator.Global(
                        expr.loc,
                        lb3,
                        ub3,
                        cpt.Operator.LogicalAnd(
                            expr.loc,
                            [
                                cpt.TemporalOperator.Global(expr.loc, lb1 - lb3, ub1 - ub3, p),
                                cpt.TemporalOperator.Global(expr.loc, lb2 - lb3, ub2 - ub3, q),
                            ],
                        )
                    )
            elif (
                cpt.is_operator(lhs, cpt.OperatorKind.FUTURE) and 
                cpt.is_operator(rhs, cpt.OperatorKind.FUTURE)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

                lhs_opnd = lhs.children[0]
                rhs_opnd = rhs.children[0]
                if str(lhs_opnd) == str(rhs_opnd):  # check for syntactic equivalence
                    # F[l1,u1]p && F[l2,u2]p = F[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub

                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.TemporalOperator.Future(expr.loc, lb2, ub2, lhs_opnd)
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.TemporalOperator.Future(expr.loc, lb1, ub1, lhs_opnd)
            elif (
                cpt.is_operator(lhs, cpt.OperatorKind.UNTIL) and
                cpt.is_operator(rhs, cpt.OperatorKind.UNTIL)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

                lhs_lhs = lhs.children[0]
                lhs_rhs = lhs.children[1]
                rhs_lhs = rhs.children[0]
                rhs_rhs = rhs.children[1]
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    new = cpt.TemporalOperator.Until(
                        expr.loc,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                        cpt.Operator.LogicalAnd(expr.loc, [lhs_lhs, rhs_lhs]),
                        lhs_rhs
                    )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if (
                cpt.is_operator(lhs, cpt.OperatorKind.FUTURE) and 
                cpt.is_operator(rhs, cpt.OperatorKind.FUTURE)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

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
                        new = cpt.TemporalOperator.Future(expr.loc, lb1, ub1, p)
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.TemporalOperator.Future(expr.loc, lb2, ub2, p)
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.TemporalOperator.Future(expr.loc, lb1, max(ub1, ub2), p)
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.TemporalOperator.Future(expr.loc, lb2, max(ub1, ub2), p)
                else:
                    # TODO: check for when lb==ub==0
                    # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                    lb3: int = min(lb1, lb2)
                    ub3: int = lb3 + min(ub1 - lb1, ub2 - lb2)

                    new = cpt.TemporalOperator.Future(
                        expr.loc,
                        lb3,
                        ub3,
                        cpt.Operator.LogicalOr(
                            expr.loc,
                            [
                                cpt.TemporalOperator.Future(expr.loc, lb1 - lb3, ub1 - ub3, p),
                                cpt.TemporalOperator.Future(expr.loc, lb2 - lb3, ub2 - ub3, q),
                            ],
                        )
                    )
            elif (
                cpt.is_operator(lhs, cpt.OperatorKind.GLOBAL) and 
                cpt.is_operator(rhs, cpt.OperatorKind.GLOBAL)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

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
                        new = cpt.TemporalOperator.Global(expr.loc, lb1, ub1, lhs_opnd)
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = cpt.TemporalOperator.Global(expr.loc, lb2, ub2, lhs_opnd)
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)

            lhs = expr.children[0]
            rhs = expr.children[1]
            if (
                isinstance(rhs, cpt.TemporalOperator)
                and rhs.operator is cpt.OperatorKind.GLOBAL
                and rhs.interval.lb == 0
                and str(lhs) == str(rhs.children[0])
            ):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                new = cpt.TemporalOperator.Global(
                    expr.loc, expr.interval.lb, expr.interval.lb + rhs.interval.ub, lhs
                )
            elif (
                isinstance(rhs, cpt.TemporalOperator)
                and rhs.operator is cpt.OperatorKind.FUTURE
                and rhs.interval.lb == 0
                and str(lhs) == str(rhs.children[0])
            ):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                new = cpt.TemporalOperator.Future(
                    expr.loc, expr.interval.lb, expr.interval.lb + rhs.interval.ub, lhs
                )

        if new:
            log.debug(
                MODULE_CODE, 2, f"\n\t{expr}\n\t==>\n\t{new}"
            )
            expr.replace(new)

    log.debug(MODULE_CODE, 1, f"Post rewrite:\n{repr(program)}")


def optimize_cse(program: cpt.Program, context: cpt.Context) -> None:
    """Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence. Applies CSE to FT/PT formulas separately."""
    log.debug(MODULE_CODE, 1, "Performing CSE")

    expr_map: dict[str, cpt.Expression]

    def _optimize_cse(expr: cpt.Expression) -> None:
        nonlocal expr_map

        if repr(expr) in expr_map:
            log.debug(MODULE_CODE, 2, f"Replacing ---- {repr(expr)[:25]}")
            expr.replace(expr_map[repr(expr)])
        else:
            log.debug(MODULE_CODE, 2, f"Visiting ----- {repr(expr)[:25]}")
            expr_map[repr(expr)] = expr

    expr_map = {}
    for expr in cpt.postorder(program.ft_spec_set, context):
        _optimize_cse(expr)

    expr_map = {}
    for expr in cpt.postorder(program.pt_spec_set, context):
        _optimize_cse(expr)

    log.debug(MODULE_CODE, 1, f"Post CSE:\n{repr(program)}")


def multi_operators_to_binary(program: cpt.Program, context: cpt.Context) -> None:
    """Converts all multi-arity operators (e.g., &&, ||, +) to binary."""
    log.debug(MODULE_CODE, 1, "Converting multi-arity operators")

    for expr in program.postorder(context):
        if not cpt.is_multi_arity_operator(expr) or len(expr.children) < 3:
            continue

        expr = cast(cpt.Operator, expr)

        new = type(expr)(expr.loc, expr.operator, expr.children[0:2], expr.type)
        for i in range(2, len(expr.children) - 1):
            new = type(expr)(
                expr.loc, expr.operator, [new, expr.children[i]], expr.type
            )
        new = type(expr)(
            expr.loc, expr.operator, [new, expr.children[-1]], expr.type
        )

        expr.replace(new)

    log.debug(MODULE_CODE, 1, f"Post multi-arity operator conversion:\n{repr(program)}")


def flatten_multi_operators(program: cpt.Program, context: cpt.Context) -> None:
    """Flattens all multi-arity operators (i.e., &&, ||, +, *)."""
    log.debug(MODULE_CODE, 1, "Flattening multi-arity operators")

    MAX_ARITY = 4

    for expr in program.postorder(context):
        if not cpt.is_multi_arity_operator(expr):
            continue

        expr = cast(cpt.Operator, expr)

        new_children = []
        for child in expr.children:
            if cpt.is_operator(child, expr.operator) and len(new_children) < MAX_ARITY:
                new_children += child.children
            else:
                new_children.append(child)
        
        new = type(expr)(expr.loc, expr.operator, new_children, expr.type)
        expr.replace(new)


    log.debug(MODULE_CODE, 1, f"Post operator flattening:\n{repr(program)}")


def sort_operands_by_pd(program: cpt.Program, context: cpt.Context) -> None:
    """Sorts all operands of commutative operators by increasing worst-case propagation delay."""
    log.debug(MODULE_CODE, 1, "Sorting operands by WPD")

    for expr in program.postorder(context):
        if not cpt.is_commutative_operator(expr):
            continue

        expr.children.sort(key=lambda child: child.wpd)

    log.debug(MODULE_CODE, 1, f"Post operand sorting:\n{repr(program)}")


def compute_atomics(program: cpt.Program, context: cpt.Context) -> None:
    """Compute atomics and store them in `context`. An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine. Syntactically equivalent expressions share the same atomic ID."""
    atomic_map: dict[str, int] = {}
    aid: int = 0

    for expr in program.postorder(context):
        if (
            expr.engine == types.R2U2Engine.TEMPORAL_LOGIC 
            or isinstance(expr, cpt.Constant) 
            or expr in context.atomic_id
        ):
            continue

        if cpt.to_prefix_str(expr) in atomic_map:
            context.atomic_id[expr] = atomic_map[cpt.to_prefix_str(expr)]
            continue

        # we just cast signals as atomics when we have no frontend
        if context.options.frontend is types.R2U2Engine.NONE:
            if isinstance(expr, cpt.Signal):
                if expr.signal_id < 0 or not context.options.assembly_enabled:
                    context.atomic_id[expr] = aid
                    atomic_map[cpt.to_prefix_str(expr)] = aid
                    aid += 1
                    continue

                context.atomic_id[expr] = expr.signal_id
                atomic_map[cpt.to_prefix_str(expr)] = expr.signal_id
                continue
        elif not isinstance(expr, cpt.Atomic):
            # add atomic node between any TL and BZ nodes
            tl_parents = [
                p for p in expr.parents if p.engine == types.R2U2Engine.TEMPORAL_LOGIC
            ]

            if expr.engine == types.R2U2Engine.BOOLEANIZER and len(tl_parents) > 0:
                new = cpt.Atomic(expr.loc, deepcopy(expr))
                for parent in tl_parents:
                    for i in range(0, len(parent.children)):
                        if id(parent.children[i]) == id(expr):
                            parent.children[i] = new
                    new.parents.append(parent)

                if cpt.to_prefix_str(new) in atomic_map:
                    context.atomic_id[new] = atomic_map[cpt.to_prefix_str(new)]
                else:
                    context.atomic_id[new] = aid
                    atomic_map[cpt.to_prefix_str(new)] = aid
                    aid += 1

    log.debug(
        MODULE_CODE, 1,
        f"Computed atomics:\n\t[{', '.join(f'({a},{i})' for a,i in context.atomic_id.items())}]",
    )


def optimize_eqsat(program: cpt.Program, context: cpt.Context) -> None:
    """Performs equality saturation over the future-time specs in `program` via egglog. See eqsat.py"""
    compute_scq_sizes(program, context)

    log.debug(MODULE_CODE, 1, "Optimizing via EQSat")

    # flatten_multi_operators(program, context)
    sort_operands_by_pd(program, context)

    if len(program.ft_spec_set.children) == 0:
        return
    
    for formula in program.ft_spec_set.children:
        formula =  cast(cpt.Formula, formula)
        e_graph = eqsat.run_egglog(formula, context)

        if not e_graph:
            continue

        old = formula.get_expr()
        new = e_graph.extract(context)

        sat_result = sat.check_equiv(old, new, context)

        if sat_result is sat.SatResult.UNSAT:
            equiv_result = "equiv"
            old.replace(new)
            compute_scq_sizes(program, context)
        elif sat_result is sat.SatResult.SAT:
            log.warning(MODULE_CODE, "Equality saturation produced non-equivalent formula, defaulting to non-optimized formula")
            equiv_result = "not-equiv"
        else:
            log.warning(MODULE_CODE, "Equality saturation could not be validated, still using optimized formula")
            equiv_result = "unknown"
            old.replace(new)
            compute_scq_sizes(program, context)
        
        context.stats.eqsat_equiv_result = equiv_result

    log.debug(MODULE_CODE, 1, f"Post EQSat:\n{repr(program)}")


def check_sat(program: cpt.Program, context: cpt.Context) -> None:
    """Checks that each specification in `program` is satisfiable and send a warning if any are either unsat or unknown."""
    log.debug(MODULE_CODE, 1, "Checking formulas satisfiability")
    
    results = sat.check_sat(program, context)

    for spec,result in results.items():
        if result is sat.SatResult.SAT:
            log.debug(MODULE_CODE, 1, f"{spec.symbol} is sat")
        elif result is sat.SatResult.UNSAT:
            log.warning(MODULE_CODE, f"{spec.symbol} is unsat")
        elif result is sat.SatResult.UNKNOWN:
            log.warning(MODULE_CODE, f"{spec.symbol} is unknown")


def compute_scq_sizes(program: cpt.Program, context: cpt.Context) -> None:
    """Computes SCQ sizes for each node."""
    total_scq_size = 0

    for expr in cpt.postorder(cast("list[cpt.Expression]", program.get_specs()), context):
        if isinstance(expr, cpt.SpecSection):
            continue

        if isinstance(expr, cpt.Formula):
            expr.scq_size = 1 + context.options.scq_constant
            expr.total_scq_size = expr.get_expr().total_scq_size + expr.scq_size

            total_scq_size += expr.scq_size

            expr.scq = (
                total_scq_size - expr.scq_size,
                total_scq_size,
            )

            continue

        if (
            expr.engine != types.R2U2Engine.TEMPORAL_LOGIC
            and expr not in context.atomic_id
        ):
            continue

        max_wpd = max([sibling.wpd for sibling in expr.get_siblings()] + [0])

        expr.scq_size = max(max_wpd - expr.bpd, 0) + 1 + context.options.scq_constant
        expr.total_scq_size = (
            sum([c.total_scq_size for c in expr.children if c.scq_size > -1])
            + expr.scq_size
        )

        total_scq_size += expr.scq_size

        expr.scq = (
            total_scq_size - expr.scq_size,
            total_scq_size,
        )

    program.total_scq_size = total_scq_size
    context.stats.total_scq_size = total_scq_size

    log.debug(MODULE_CODE, 1, f"Program SCQ size: {total_scq_size}")


# A Pass is a function with the signature:
#    pass(program, context) -> None
Pass = Callable[[cpt.Program, cpt.Context], None]


# This list is ORDER-SENSITIVE 
# We resolve struct accesses twice in the case that a struct is an element of an array and an array
# is a member of a struct
pass_list: list[Pass] = [
    expand_definitions,
    convert_function_calls_to_structs,
    resolve_contracts,
    resolve_struct_accesses,
    unroll_set_aggregation,
    resolve_struct_accesses,
    resolve_array_accesses,
    resolve_struct_accesses,
    compute_atomics, 
    optimize_rewrite_rules,
    optimize_eqsat,
    compute_atomics, 
    to_nnf,
    to_bnf,
    remove_extended_operators,
    multi_operators_to_binary,
    optimize_cse,
    check_sat,
    compute_scq_sizes, 
]


def setup(opts: options.Options) -> None:
    """Sets up the passes for the compiler."""
    log.debug(MODULE_CODE, 1, "Setting up passes")

    if opts.spec_format == options.SpecFormat.MLTL:
        pass_list.remove(expand_definitions)
        pass_list.remove(convert_function_calls_to_structs)
        pass_list.remove(resolve_contracts)
        pass_list.remove(resolve_struct_accesses)
        pass_list.remove(unroll_set_aggregation)
        pass_list.remove(resolve_struct_accesses)
        pass_list.remove(resolve_array_accesses)
        pass_list.remove(resolve_struct_accesses)

    if not opts.enable_rewrite:
        pass_list.remove(optimize_rewrite_rules)

    if not opts.enable_cse:
        pass_list.remove(optimize_cse)

    if opts.enable_extops:
        pass_list.remove(remove_extended_operators)

    if opts.enable_eqsat:
        if optimize_rewrite_rules in pass_list:
            pass_list.remove(optimize_rewrite_rules)
        if optimize_cse in pass_list:
            pass_list.remove(optimize_cse)
        if remove_extended_operators in pass_list:
            pass_list.remove(remove_extended_operators)

        # since optimize_egraph flattens operators, no need to convert them to binary
        pass_list.remove(multi_operators_to_binary)
    else: # not enable_egraph
        pass_list.remove(optimize_eqsat)
        
    if not opts.enable_nnf:
        pass_list.remove(to_nnf)

    if not opts.enable_bnf:
        pass_list.remove(to_bnf)

    if not opts.enable_sat:
        pass_list.remove(check_sat)
