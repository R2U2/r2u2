from __future__ import annotations
from typing import cast, Callable

from c2po import cpt, types, log, options

MODULE_CODE = "SIM"

try:
    import z3
except ImportError:
    raise ImportError("z3 not found")

def cpt_to_z3(
    expr: cpt.Expression,
    context: cpt.Context,
    z3_vars: dict[str, z3.FuncDeclRef],
) -> Callable[[z3.ExprRef], z3.ExprRef]:
    """
    Convert a CPT expression to a Z3 expression, which is a function that takes an integer and
    returns a Z3 expression representing the value of the expression at that time step.
    """
    if isinstance(expr, cpt.Signal):
        return z3_vars[expr.symbol]
    elif isinstance(expr, cpt.Atomic):
        return lambda k: cpt_to_z3(expr.children[0], context, z3_vars)(k)
    elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type):
        return lambda k: z3.BoolVal(expr.value)
    elif isinstance(expr, cpt.Constant) and types.is_integer_type(expr.type):
        return lambda k: z3.IntVal(expr.value)
    elif isinstance(expr, cpt.Constant) and types.is_float_type(expr.type):
        return lambda k: z3.RealVal(expr.value)
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
        return lambda k: cast(z3.ExprRef, z3.Not(cpt_to_z3(expr.children[0], context, z3_vars)(k)))
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
        return lambda k: cast(
            z3.ExprRef, z3.And([cpt_to_z3(child, context, z3_vars)(k) for child in expr.children])
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
        return lambda k: cast(
            z3.ExprRef, z3.Or([cpt_to_z3(child, context, z3_vars)(k) for child in expr.children])
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            == cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            != cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            > cpt_to_z3(expr.children[1], context, z3_vars)(k),
        ) 
    elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            < cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            >= cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            <= cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
        return lambda k: cast(
            z3.ExprRef,
            z3.Sum([cpt_to_z3(child, context, z3_vars)(k) for child in expr.children])
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            - cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
        return lambda k: cast(
            z3.ExprRef,
            z3.Product([cpt_to_z3(child, context, z3_vars)(k) for child in expr.children])
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            / cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            % cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
        if types.is_integer_type(expr.children[0].type):
            return lambda k: cast(z3.ExprRef, z3.Int(-1) * cpt_to_z3(expr.children[0], context, z3_vars)(k))
        elif types.is_float_type(expr.children[0].type):
            return lambda k: cast(z3.ExprRef, z3.Real(-1) * cpt_to_z3(expr.children[0], context, z3_vars)(k))
        else:
            raise ValueError(f"Bad type: {expr.children[0].type}")
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_POWER):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            ** cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SQRT):
        return lambda k: cast(
            z3.ExprRef,
            z3.Sqrt(cpt_to_z3(expr.children[0], context, z3_vars)(k))
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ABS):
        return lambda k: cast(
            z3.ExprRef,
            z3.Abs(cpt_to_z3(expr.children[0], context, z3_vars)(k))
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.SHIFT_LEFT):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            << cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.SHIFT_RIGHT):
        return lambda k: cast(
            z3.ExprRef,
            cpt_to_z3(expr.children[0], context, z3_vars)(k) # type: ignore
            >> cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
        expr = cast(cpt.TemporalOperator, expr)
        lb = expr.interval.lb
        ub = expr.interval.ub
        if lb != ub:
            raise ValueError(f"Global operator with non-singleton interval: {expr}, {type(expr)}, {expr.type}\n"  
                              "\nWas the expression unrolled?")

        return lambda k: cpt_to_z3(expr.children[0], context, z3_vars)(k + z3.IntVal(lb))
    elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
        expr = cast(cpt.TemporalOperator, expr)
        lb = expr.interval.lb
        ub = expr.interval.ub
        if lb != ub:
            raise ValueError(f"Future operator with non-singleton interval: {expr}, {type(expr)}, {expr.type}\n"  
                              "\nWas the expression unrolled?")

        return lambda k: cpt_to_z3(expr.children[0], context, z3_vars)(k + z3.IntVal(lb))
    else:
        raise ValueError(f"Unsupported expression: {expr}, {type(expr)}, {expr.type}\n"  
                          "\nWas the expression unrolled?")


def simulate_sat(program: cpt.Program, context: cpt.Context, k: int, sat: bool) -> list[list[str]]:
    """
    Simulate a CPT program, returning a satisfying trace if `sat` is True. The approach is naive:
    - Generate an uninterpreted function for each signal.
    - Create a Z3 expression for each spec, which is a function that takes an integer and returns a
      Z3 expression representing the value of the spec at that time step.
    - For each time step in 0..k:
        - Add the constraints for the spec at k.
        - Check satisfiability.
        - If unsat, pop the constraints and continue.
        - If sat, continue
    - By the end (assuming sat at least once), we have a model that satisfies the spec for as many 
      time steps as possible given the constraints.

    TODO: A more efficient approach would be to use formula progression, but this naive approach
    is good enough for now.
    """
    z3_vars = {}
    for sig, typ in context.signals.items():
        if isinstance(typ, types.BoolType):
            z3_vars[sig] = z3.Function(sig, z3.IntSort(), z3.BoolSort())
        elif isinstance(typ, types.IntType):
            z3_vars[sig] = z3.Function(sig, z3.IntSort(), z3.IntSort())
        elif isinstance(typ, types.FloatType):
            z3_vars[sig] = z3.Function(sig, z3.IntSort(), z3.RealSort())
        else:
            raise ValueError(f"Unsupported signal type: {typ}")

    z3_exprs = []
    for spec in [s for s in program.get_specs() if isinstance(s, cpt.Formula)]:
        # We unroll the temporal operators to avoid quantifier alternation; so long as the interval
        # sizes are <1000 or so this is fine.
        unrolled = cpt.unroll_temporal_operators(spec.get_expr(), context)
        z3_exprs.append(cpt_to_z3(unrolled, context, z3_vars))

    s = z3.Solver()
    for i in range(k):
        log.debug(MODULE_CODE, 1, f"k = {i}")
        s.push()

        constraint = (
            z3.And([z3_expr(z3.IntVal(i)) for z3_expr in z3_exprs])
            if sat
            else z3.Not(z3.And([z3_expr(z3.IntVal(i)) for z3_expr in z3_exprs]))
        )
        s.add(constraint)

        # FIXME: Set the initial guesses for the signals to some random values.
        # for sig, typ in z3_vars.items(): 
        #     if isinstance(typ, types.BoolType):
        #         s.set_initial_value(z3_vars[sig](z3.IntVal(i)), z3.BoolVal(random.random() < 0.5))
        #     elif isinstance(typ, types.IntType):
        #         s.set_initial_value(z3_vars[sig](z3.IntVal(i)), z3.IntVal(random.randint(0, 1000)))
        #     elif isinstance(typ, types.FloatType):
        #         s.set_initial_value(z3_vars[sig](z3.IntVal(i)), z3.RealVal(random.random()))
        #     else:
        #         raise ValueError(f"Unsupported signal type: {typ}")

        if s.check() != z3.sat:
            log.warning(MODULE_CODE, f"unsat at k = {i}")
            s.pop()
            continue

    trace = [[sig for sig in z3_vars]]
    for i in range(k):
        trace.append(
            [
                str(s.model().eval(z3_vars[sig](z3.IntVal(i)), model_completion=True))
                for sig in z3_vars
            ]
        )
    return trace

def simulate_random(program: cpt.Program, context: cpt.Context, k: int) -> list[list[str]]:
    """
    Simulate a CPT program with random values.
    """
    trace = [[sig for sig in context.signals]]
    # FIXME: Implement this
    return trace

def simulate(program: cpt.Program, context: cpt.Context, k: int, mode: options.SimulateMode) -> list[list[str]]:
    """
    Simulate a CPT program.

    FIXME: Shall we consider a way to model the system
    """
    if k < 0:
        k = program.max_wpd + 1

    if mode == options.SimulateMode.SAT:
        return simulate_sat(program, context, k, True)
    elif mode == options.SimulateMode.UNSAT:
        return simulate_sat(program, context, k, False)
    elif mode == options.SimulateMode.RANDOM:
        return simulate_random(program, context, k)
    else:
        raise ValueError(f"Invalid simulate mode: {mode}")
