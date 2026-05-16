from __future__ import annotations
from typing import Any, cast
from c2po import cpt, log, command, types

def to_bnf(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators."""
    lhs: cpt.Expression
    rhs: cpt.Expression
    operand: cpt.Expression
    bounds: cpt.ConcreteInterval

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
            lhs = expr.children[0]
            rhs = expr.children[1]
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
            lhs = expr.children[0]
            rhs = expr.children[1]
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
            operand = expr.children[0]
            bounds = expr.interval
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
            operand = expr.children[0]
            bounds = expr.interval
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
            lhs = expr.children[0]
            rhs = expr.children[1]
            bounds = expr.interval
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

    log.debug(1, f"post BNF conversion:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

to_bnf_command = command.Command(
    name="to_bnf",
    description="Convert program formulas to Boolean Normal Form (BNF)",
    options=[],
    func=to_bnf,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(to_bnf_command)

def to_nnf(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    lhs: cpt.Expression
    rhs: cpt.Expression
    operand: cpt.Expression
    bounds: cpt.ConcreteInterval

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
                lhs = operand.children[0]
                rhs = operand.children[1]

                # ! (p -> q) |-> ! (!p || q) |-> p && !q
                expr.replace(
                    cpt.Operator.LogicalAnd(
                        expr.loc, [lhs, cpt.Operator.LogicalNegate(lhs.loc, rhs)]
                    )
                )
            elif cpt.is_operator(operand, cpt.OperatorKind.LOGICAL_XOR):
                lhs = operand.children[0]
                rhs = operand.children[1]
                
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
                lhs = operand.children[0]
                rhs = operand.children[1]
                
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
                bounds = operand.interval

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
                bounds = operand.interval

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

                lhs = operand.children[0]
                rhs = operand.children[1]
                
                bounds = operand.interval

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

                lhs = operand.children[0]
                rhs = operand.children[1]

                bounds = operand.interval

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
            lhs = expr.children[0]
            rhs = expr.children[1]

            # p -> q = !p || q
            expr.replace(
                cpt.Operator.LogicalOr(
                    expr.loc, [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs]
                )
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_XOR):
            lhs = expr.children[0]
            rhs = expr.children[1]
            
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

    log.debug(1, f"post NNF conversion:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

to_nnf_command = command.Command(
    name="to_nnf",
    description="Convert program formulas to Negative Normal Form (NNF)",
    options=[],
    func=to_nnf,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(to_nnf_command)

def multi_operators_to_binary(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Converts all multi-arity operators (e.g., &&, ||, +) to binary.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
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

    log.debug(1, f"post multi-arity operator conversion:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

multi_operators_to_binary_command = command.Command(
    name="multi_operators_to_binary",
    description="Convert all multi-arity operators (e.g., &&, ||, +) to binary",
    options=[],
    func=multi_operators_to_binary,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(multi_operators_to_binary_command)

def flatten_multi_operators(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Flattens all multi-arity operators (i.e., &&, ||, +, *).
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
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

    log.debug(1, f"post operator flattening:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

flatten_multi_operators_command = command.Command(
    name="flatten_multi_operators",
    description="Flatten all multi-arity operators (i.e., &&, ||, +, *)",
    options=[],
    func=flatten_multi_operators,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(flatten_multi_operators_command)

def remove_extended_operators(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Removes extended operators (xor, ->, F, G, O, H) from the program.
    Also makes all operators binary.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    lhs: cpt.Expression
    rhs: cpt.Expression
    operand: cpt.Expression
    interval: cpt.ConcreteInterval

    if not multi_operators_to_binary(program, context, options):
        return command.ReturnCode.ERROR

    for expr in program.postorder(context):
        if not isinstance(expr, cpt.Operator):
            continue

        if expr.operator is cpt.OperatorKind.LOGICAL_XOR:
            lhs = expr.children[0]
            rhs = expr.children[1]
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
            lhs = expr.children[0]
            rhs = expr.children[1]
            # p -> q = !p || q)
            expr.replace(
                cpt.Operator.LogicalOr(
                    expr.loc, [cpt.Operator.LogicalNegate(lhs.loc, lhs), rhs]
                ),
            )
        elif expr.operator is cpt.OperatorKind.FUTURE:
            expr = cast(cpt.TemporalOperator, expr)

            operand = expr.children[0]

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

            operand = expr.children[0]

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

            operand = expr.children[0]

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

            operand = expr.children[0]

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

    log.debug(1, f"post extended operator removal:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

remove_extended_operators_command = command.Command(
    name="remove_extended_operators",
    description="Remove extended operators (xor, ->, F, G, O, H) from the program and make all operators binary",
    options=[],
    func=remove_extended_operators,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(remove_extended_operators_command)

def sort_operands_by_pd(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Sorts all operands of commutative operators by increasing worst-case propagation delay.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for expr in program.postorder(context):
        if not cpt.is_commutative_operator(expr):
            continue

        expr.children.sort(key=lambda child: child.wpd)

    log.debug(1, f"post operand sorting:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

sort_operands_by_pd_command = command.Command(
    name="sort_operands_by_pd",
    description="Sort all operands of commutative operators by increasing worst-case propagation delay",
    options=[],
    func=sort_operands_by_pd,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(sort_operands_by_pd_command)

def remove_release_operators(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Removes release operators (R) from the program.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for expr in program.postorder(context):
        if not cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            continue

        expr = cast(cpt.TemporalOperator, expr)

        expr.replace(
            cpt.Operator.LogicalNegate(
                expr.loc,
                cpt.TemporalOperator.Until(
                    expr.loc,
                    expr.interval.lb,
                    expr.interval.ub,
                    cpt.Operator.LogicalNegate(expr.loc, expr.children[0]),
                    cpt.Operator.LogicalNegate(expr.loc, expr.children[1])
                )
            )
        )
        
    log.debug(1, f"post release operator removal:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

remove_release_operators_command = command.Command(
    name="remove_release_operators",
    description="Remove release operators (R) from the program",
    options=[],
    func=remove_release_operators,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(remove_release_operators_command)

def convert_atomics_to_signals(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Converts all atomics to signals.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    replaced_count = 0

    # Replace via parent->children edges from the live AST, rather than relying on Atomic.parents,
    # which may be stale after earlier transformations.
    for expr in program.preorder(context):
        for i, child in enumerate(expr.children):
            if not isinstance(child, cpt.Atomic):
                continue

            if child not in context.atomic_id_map:
                log.error(f"atomic {repr(child)} not found in atomic ID map")
                return command.ReturnCode.ERROR

            aid = context.atomic_id_map[child]
            signal = cpt.Signal(child.loc, f"a{aid}", types.BoolType())
            signal.signal_id = aid
            expr.children[i] = signal
            signal.parents.add(expr)
            replaced_count += 1

    log.debug(2, f"replaced {replaced_count} atomic nodes with signals")
    log.debug(1, f"post atomic to signal conversion:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

convert_atomics_to_signals_command = command.Command(
    name="convert_atomics_to_signals",
    description="Convert all atomics to signals",
    options=[],
    func=convert_atomics_to_signals,
    guards=[command.WELL_TYPED, command.DESUGARED, command.COMPUTED_ATOMICS],
)
command.CommandRegistry.register(convert_atomics_to_signals_command)
