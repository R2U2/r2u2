from __future__ import annotations
import enum
import random
from typing import Any, Callable, Optional, cast

from c2po import cpt, types, log, command


class SimulateMode(enum.Enum):
    SAT = "sat"
    UNSAT = "unsat"
    RANDOM = "random"


def _import_z3() -> Any:
    """Import the z3 Python package, raising a clear error if it is not installed."""
    try:
        import z3
    except ImportError as exc:
        raise ImportError(
            "z3 Python package not found; install with 'pip install z3-solver'"
        ) from exc
    return z3


def _format_z3_value(value: Any, typ: types.Type, z3: Any) -> str:
    """Format a Z3 model value as an R2U2 CSV cell."""
    if types.is_bool_type(typ):
        return "1" if z3.is_true(value) else "0"
    if types.is_float_type(typ):
        try:
            return value.as_decimal(6).rstrip("?")
        except AttributeError:
            return str(value)
    return str(value)


def cpt_to_z3(
    expr: cpt.Expression,
    context: cpt.Context,
    z3_vars: dict[str, Any],
) -> Callable[[Any], Any]:
    """
    Convert a CPT expression to a Z3 expression, which is a function that takes an integer and
    returns a Z3 expression representing the value of the expression at that time step.
    """
    z3 = _import_z3()

    if isinstance(expr, cpt.Signal):
        return z3_vars[expr.symbol]
    elif isinstance(expr, (cpt.Atomic, cpt.Formula)):
        return lambda k: cpt_to_z3(expr.children[0], context, z3_vars)(k)
    elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type):
        return lambda k: z3.BoolVal(expr.value)
    elif isinstance(expr, cpt.Constant) and types.is_integer_type(expr.type):
        return lambda k: z3.IntVal(expr.value)
    elif isinstance(expr, cpt.Constant) and types.is_float_type(expr.type):
        return lambda k: z3.RealVal(expr.value)
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
        return lambda k: z3.Not(cpt_to_z3(expr.children[0], context, z3_vars)(k))
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
        return lambda k: z3.And(
            [cpt_to_z3(child, context, z3_vars)(k) for child in expr.children]
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
        return lambda k: z3.Or(
            [cpt_to_z3(child, context, z3_vars)(k) for child in expr.children]
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_XOR):
        def xor_at(k: Any) -> Any:
            result = cpt_to_z3(expr.children[0], context, z3_vars)(k)
            for child in expr.children[1:]:
                result = z3.Xor(result, cpt_to_z3(child, context, z3_vars)(k))
            return result
        return xor_at
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
        return lambda k: z3.Implies(
            cpt_to_z3(expr.children[0], context, z3_vars)(k),
            cpt_to_z3(expr.children[1], context, z3_vars)(k),
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            == cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            == cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            != cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            > cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            < cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            >= cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            <= cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
        return lambda k: z3.Sum(
            [cpt_to_z3(child, context, z3_vars)(k) for child in expr.children]
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            - cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
        return lambda k: z3.Product(
            [cpt_to_z3(child, context, z3_vars)(k) for child in expr.children]
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            / cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            % cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
        if types.is_integer_type(expr.children[0].type):
            return lambda k: z3.IntVal(-1) * cpt_to_z3(expr.children[0], context, z3_vars)(k)
        elif types.is_float_type(expr.children[0].type):
            return lambda k: z3.RealVal(-1) * cpt_to_z3(expr.children[0], context, z3_vars)(k)
        else:
            raise ValueError(f"Bad type: {expr.children[0].type}")
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_POWER):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            ** cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SQRT):
        return lambda k: z3.Sqrt(cpt_to_z3(expr.children[0], context, z3_vars)(k))
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ABS):
        return lambda k: z3.Abs(cpt_to_z3(expr.children[0], context, z3_vars)(k))
    elif cpt.is_operator(expr, cpt.OperatorKind.SHIFT_LEFT):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            << cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.SHIFT_RIGHT):
        return lambda k: (
            cpt_to_z3(expr.children[0], context, z3_vars)(k)
            >> cpt_to_z3(expr.children[1], context, z3_vars)(k)
        )
    elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
        expr = cast(cpt.TemporalOperator, expr)
        lb = expr.interval.lb
        ub = expr.interval.ub
        if lb != ub:
            raise ValueError(
                f"Global operator with non-singleton interval: {expr}\n"
                "Was the expression unrolled?"
            )
        return lambda k: cpt_to_z3(expr.children[0], context, z3_vars)(k + z3.IntVal(lb))
    elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
        expr = cast(cpt.TemporalOperator, expr)
        lb = expr.interval.lb
        ub = expr.interval.ub
        if lb != ub:
            raise ValueError(
                f"Future operator with non-singleton interval: {expr}\n"
                "Was the expression unrolled?"
            )
        return lambda k: cpt_to_z3(expr.children[0], context, z3_vars)(k + z3.IntVal(lb))
    else:
        raise ValueError(
            f"Unsupported expression: {expr}, {type(expr)}, {expr.type}\n"
            "Was the expression unrolled?"
        )


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
    z3 = _import_z3()

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
        log.debug(1, f"k = {i}")
        s.push()

        if z3_exprs:
            constraint = (
                z3.And([z3_expr(z3.IntVal(i)) for z3_expr in z3_exprs])
                if sat
                else z3.Not(z3.And([z3_expr(z3.IntVal(i)) for z3_expr in z3_exprs]))
            )
        else:
            constraint = z3.BoolVal(True)
        s.add(constraint)

        if s.check() != z3.sat:
            log.warning(f"unsat at k = {i}")
            s.pop()
            continue

    header = list(z3_vars)
    if k <= 0:
        return [header]

    if s.check() != z3.sat:
        log.error("no model available for simulated trace")
        return [header]

    model = s.model()
    trace = [header]
    for i in range(k):
        trace.append(
            [
                _format_z3_value(
                    model.eval(z3_vars[sig](z3.IntVal(i)), model_completion=True),
                    context.signals[sig],
                    z3,
                )
                for sig in z3_vars
            ]
        )
    return trace


def simulate_random(program: cpt.Program, context: cpt.Context, k: int) -> list[list[str]]:
    """Simulate a CPT program with random signal values."""
    header = list(context.signals)
    trace = [header]
    for _ in range(max(k, 0)):
        row = []
        for _, typ in context.signals.items():
            if types.is_bool_type(typ):
                row.append(str(random.randint(0, 1)))
            elif types.is_float_type(typ):
                row.append(f"{random.random():.5f}")
            elif types.is_integer_type(typ):
                row.append(str(random.randint(0, 1000)))
            else:
                raise ValueError(f"Unsupported signal type: {typ}")
        trace.append(row)
    return trace


def simulate(
    program: cpt.Program, context: cpt.Context, k: int, mode: SimulateMode
) -> list[list[str]]:
    """
    Simulate a CPT program.

    FIXME: Shall we consider a way to model the system
    """
    if k < 0:
        k = program.max_wpd + 1

    if mode == SimulateMode.SAT:
        return simulate_sat(program, context, k, True)
    elif mode == SimulateMode.UNSAT:
        return simulate_sat(program, context, k, False)
    elif mode == SimulateMode.RANDOM:
        return simulate_random(program, context, k)
    else:
        raise ValueError(f"Invalid simulate mode: {mode}")


def _trace_to_csv(trace: list[list[str]]) -> list[str]:
    """Convert a header-plus-rows trace into CSV lines with a `#` header."""
    if not trace:
        return []
    lines = [f"#{','.join(trace[0])}"]
    lines.extend(",".join(row) for row in trace[1:])
    return lines


def simulate_command(
    program: cpt.Program, context: cpt.Context, options: dict[str, Any]
) -> command.ReturnCode:
    """
    Simulate a program and produce a CSV trace.

    `options` is a dictionary of options that must contain the following keys:
    - `mode`: Simulation mode (`sat`, `unsat`, or `random`)
    - `k`: Trace length. If negative, uses the maximum worst-case propagation delay plus one.
    - `output`: Optional path to write the trace file
    - `print`: Whether to print the trace to the console
    """
    try:
        mode = SimulateMode(options["mode"])
    except ValueError:
        log.error(f"invalid simulate mode: {options['mode']}")
        return command.ReturnCode.ERROR

    k = options["k"]
    output_file: Optional[str] = options["output"]
    print_trace: bool = options["print"]

    try:
        trace = simulate(program, context, k, mode)
    except ImportError as e:
        log.error(str(e))
        return command.ReturnCode.ERROR
    except ValueError as e:
        log.error(str(e))
        return command.ReturnCode.ERROR

    output_lines = _trace_to_csv(trace)
    context.trace = output_lines
    context.trace_length = max(len(output_lines) - 1, 0)

    if output_file is not None:
        with open(output_file, "w") as f:
            f.write("\n".join(output_lines))
            if output_lines:
                f.write("\n")

    if print_trace:
        print("\n".join(output_lines))

    return command.ReturnCode.SUCCESS


simulate_cmd = command.Command(
    name="simulate",
    description="Simulate a program and generate a CSV trace (sat/unsat modes require the z3 Python package)",
    options=[
        {
            "name": "mode",
            "description": "Simulation mode: sat generates a satisfying trace, unsat a violating trace, random unconstrained values",
            "required": True,
            "type": str,
            "default": None,
            "choices": [member.value for member in SimulateMode],
        },
        {
            "name": "k",
            "description": "Trace length. If negative, uses the maximum worst-case propagation delay plus one",
            "required": False,
            "type": int,
            "default": -1,
            "choices": None,
        },
        {
            "name": "output",
            "description": "Path to write the generated CSV trace",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "print",
            "description": "Print the generated trace to the console",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
    ],
    func=simulate_command,
    guards=[command.DESUGARED],
)
command.CommandRegistry.register(simulate_cmd)
