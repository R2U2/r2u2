from __future__ import annotations
import copy
from typing import cast

from c2po import cpt, log, sat, types

MODULE_CODE = "FO"

empty_context = cpt.Context()


def init_variables(expr: cpt.Expression) -> None:
    """Set the types of variables in the given first-order expression to ints."""
    global empty_context
    for subexpr in cpt.postorder(expr, empty_context):
        if isinstance(subexpr, cpt.Variable):
            subexpr.type = types.IntType()
            subexpr.set_timestamp(0)


def annotate_vars(expr: cpt.Expression, i: int) -> cpt.Expression:
    """Annotate variables in the given first-order expression."""
    global empty_context
    for subexpr in cpt.postorder(expr, empty_context):
        if isinstance(subexpr, cpt.Variable):
            subexpr.set_index(i)
    return expr


def timestamp_vars(expr: cpt.Expression, tau: int) -> cpt.Expression:
    """Timestamp variables in the given first-order expression."""
    global empty_context
    for subexpr in cpt.postorder(expr, empty_context):
        if isinstance(subexpr, cpt.Variable):
            subexpr.set_timestamp(tau)
    return expr


def expr_is_ground(expr: cpt.Expression) -> bool:
    """Check if the given first-order expression is ground."""
    global empty_context
    for subexpr in cpt.postorder(expr, empty_context):
        if isinstance(subexpr, cpt.Quantifier):
            return False
    return True


def eliminate_quantifiers(expr: cpt.Formula, bounds: dict[str, int]) -> cpt.Formula:
    """Eliminate quantifiers from the given first-order expression."""
    log.debug(MODULE_CODE, 1, f"Eliminating quantifiers from first-order expression {expr}")
    global empty_context

    for subexpr in cpt.postorder(expr, empty_context):
        if isinstance(subexpr, cpt.Quantifier) and subexpr.operator == cpt.QuantifierKind.FORALL:
            log.debug(MODULE_CODE, 2, f"Eliminating forall quantifier: {subexpr}")
            subexpr.replace(
                cpt.Operator.LogicalAnd(
                    subexpr.loc,
                    [
                        annotate_vars(copy.deepcopy(subexpr.get_expr()), i)
                        for i in range(0, bounds[subexpr.set_pred])
                    ],
                )
            )
        elif isinstance(subexpr, cpt.Quantifier) and subexpr.operator == cpt.QuantifierKind.EXISTS:
            log.debug(MODULE_CODE, 2, f"Eliminating exists quantifier: {subexpr}")
            subexpr.replace(
                cpt.Operator.LogicalOr(
                    subexpr.loc,
                    [
                        annotate_vars(copy.deepcopy(subexpr.get_expr()), i)
                        for i in range(0, bounds[subexpr.set_pred])
                    ],
                )
            )

    log.debug(MODULE_CODE, 1, f"Quantifier-eliminated expression: {expr}")

    return expr


def unroll_temporal_operators(expr: cpt.Formula) -> cpt.Formula:
    """Unroll temporal operators in the given first-order expression."""
    log.debug(MODULE_CODE, 1, f"Unrolling temporal operators in first-order expression {expr}")
    global empty_context

    for subexpr in cpt.postorder(expr, empty_context):
        if cpt.is_operator(subexpr, cpt.OperatorKind.FUTURE) and not expr_is_ground(subexpr):
            log.debug(MODULE_CODE, 2, f"Unrolling: {subexpr}")
            subexpr.replace(
                cpt.Operator.LogicalOr(
                    subexpr.loc,
                    [
                        cpt.TemporalOperator.Future(
                            subexpr.loc,
                            tau, tau,
                            timestamp_vars(
                                copy.deepcopy(subexpr.children[0]),
                                tau
                            )
                        )
                        for tau in range(0, subexpr.wpd+1)
                    ]
                )
            )
        elif cpt.is_operator(subexpr, cpt.OperatorKind.GLOBAL) and not expr_is_ground(subexpr):
            log.debug(MODULE_CODE, 2, f"Unrolling: {subexpr}")
            subexpr.replace(
                cpt.Operator.LogicalAnd(
                    subexpr.loc,
                    [   
                        cpt.TemporalOperator.Global(
                            subexpr.loc,
                            tau, tau,
                            timestamp_vars(
                                copy.deepcopy(subexpr.children[0]),
                                tau
                            )
                        )
                        for tau in range(subexpr.bpd, subexpr.wpd+1)
                    ]
                )
            )
        elif cpt.is_operator(subexpr, cpt.OperatorKind.UNTIL) and not expr_is_ground(subexpr):
            log.debug(MODULE_CODE, 2, f"Unrolling: {subexpr}")
            subexpr = cast(cpt.TemporalOperator, subexpr)
            subexpr.replace(
                cpt.Operator.LogicalOr(
                    subexpr.loc,
                    [
                        timestamp_vars(
                            copy.deepcopy(subexpr.children[0]),
                            subexpr.interval.lb
                        ),
                        cpt.Operator.LogicalAnd(
                            subexpr.loc,
                            [
                                timestamp_vars(
                                    copy.deepcopy(subexpr.children[1]),
                                    subexpr.interval.lb
                                ),
                                cpt.TemporalOperator.Until(
                                    subexpr.loc,
                                    subexpr.interval.lb+1,
                                    subexpr.interval.ub,
                                    subexpr.children[0],
                                    subexpr.children[1]
                                )
                            ]
                        ) if subexpr.interval.lb < subexpr.interval.ub else timestamp_vars(
                            copy.deepcopy(subexpr.children[1]),
                            subexpr.interval.lb
                        )
                    ]
                )
            )

    log.debug(MODULE_CODE, 1, f"Unrolled expression: {expr}")

    return expr


def check_sat(formula: cpt.Formula, bounds: dict[str, int]) -> sat.SatResult:
    """Check if the given first-order expression is satisfiable given the bounds."""
    log.debug(MODULE_CODE, 1, f"Checking satisfiability of first-order formula {formula}")
    global empty_context
    init_variables(formula)

    new = unroll_temporal_operators(formula)
    new = eliminate_quantifiers(new, bounds)
    expr = new.get_expr()
    return sat.check_sat_expr(expr, empty_context)
