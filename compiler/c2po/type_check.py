from __future__ import annotations

from c2po import log
from c2po import types
from c2po import cpt


def type_check_expr(expr: cpt.Expression, context: cpt.Context) -> bool:
    status = True

    if isinstance(expr, cpt.Specification):
        status = status and type_check_expr(expr.get_expr(), context)
    elif isinstance(expr, cpt.Constant):
        pass
    elif isinstance(expr, cpt.Signal):
        if context.assembly_enabled and expr.symbol not in context.signal_mapping:
            status = False
            log.error(
                f"Mapping does not contain signal '{expr.symbol}'.",
                __name__,
                expr.loc
            )

        if expr.symbol in context.signal_mapping:
            expr.signal_id = context.signal_mapping[expr.symbol]

        expr.type = context.signals[expr.symbol]
    elif isinstance(expr, cpt.AtomicChecker):
        if expr.symbol not in context.atomic_checkers:
            status = False
            log.error(f"Atomic checker '{expr.symbol}' not defined.", __name__, expr.loc)
    elif isinstance(expr, cpt.Variable):
        symbol = expr.symbol
        if symbol in context.variables:
            expr.type = context.variables[symbol]
        elif symbol in context.definitions:
            expr.type = context.definitions[symbol].type
        elif symbol in context.structs:
            log.error(
                "Defined structs may not be used as variables. Maybe you mean to declare the struct first?",
                __name__,
                expr.loc
            )
            status = False
        elif symbol in context.atomic_checkers:
            expr.type = types.BoolType(False)
        elif symbol in context.specifications:
            expr.type = types.BoolType(False)
        elif symbol in context.contracts:
            log.error(
                f"Contracts not allowed as subexpressions ('{symbol}').",
                __name__,
                expr.loc
            )
            status = False
        else:
            log.error(f"Symbol '{symbol}' not recognized.", __name__, expr.loc)
            status = False
    elif isinstance(expr, cpt.FunctionCall):
        # For now, this can only be a struct instantiation
        if (
            expr.symbol not in context.structs
            and expr.symbol not in context.atomic_checker_filters
        ):
            log.error(f"General functions unsupported.\n\t{expr}", __name__, expr.loc)
            status = False

        for arg in expr.get_operands():
            status = status and type_check_expr(arg, context)

        if expr.symbol in context.structs:
            expr.type = types.StructType(False, expr.symbol)
    elif isinstance(expr, cpt.RelationalOperator):
        lhs: cpt.Expression = expr.get_lhs()
        rhs: cpt.Expression = expr.get_rhs()
        status = status and type_check_expr(lhs, context)
        status = status and type_check_expr(rhs, context)

        if lhs.type != rhs.type:
            status = False
            log.error(
                f"Invalid operands for '{expr.symbol}', must be of same type (found '{lhs.type}' and '{rhs.type}')\n\t{expr}",
                __name__,
                expr.loc
            )

        expr.type = types.BoolType(lhs.type.is_const and rhs.type.is_const)
    elif isinstance(expr, cpt.ArithmeticOperator):
        is_const: bool = True

        if context.implementation != types.R2U2Implementation.C:
            status = False
            log.error(
                f"Arithmetic operators only support in C version of R2U2.\n\t{expr}",
                __name__,
                expr.loc
            )

        if not context.booleanizer_enabled:
            status = False
            log.error(
                f"Found Booleanizer expression, but Booleanizer expressions disabled\n\t{expr}",
                __name__,
                expr.loc
            )

        for c in expr.get_operands():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const

        t: types.Type = expr.get_operand(0).type
        t.is_const = is_const

        if isinstance(expr, cpt.ArithmeticDivide):
            rhs: cpt.Expression = expr.get_rhs()
            if isinstance(rhs, cpt.Constant) and rhs.get_value() == 0:
                status = False
                log.error(f"Divide by zero\n\t{expr}", __name__, expr.loc)

        for c in expr.get_operands():
            if c.type != t:
                status = False
                log.error(
                    f"Operand of '{expr}' must be of homogeneous type (found '{c.type}' and '{t}')",
                __name__,
                expr.loc
                )

        expr.type = t
    elif isinstance(expr, cpt.BitwiseOperator):
        is_const: bool = True

        if context.implementation != types.R2U2Implementation.C:
            status = False
            log.error(
                f"Bitwise operators only support in C version of R2U2.\n\t{expr}",
                __name__,
                expr.loc
            )

        if not context.booleanizer_enabled:
            status = False
            log.error(
                f"Found context.booleanizer_enabled expression, but Booleanizer expressions disabled\n\t{expr}",
                __name__,
                expr.loc
            )

        t: types.Type = types.NoType()
        for c in expr.get_operands():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const
            t = c.type

        t.is_const = is_const

        for c in expr.get_operands():
            if c.type != t or not types.is_integer_type(c.type):
                status = False
                log.error(
                    f"Invalid operands for '{expr.symbol}', found '{c.type}' ('{c}') but expected '{t}'\n\t{expr}",
                __name__,
                expr.loc
                )

        expr.type = t
    elif isinstance(expr, cpt.LogicalOperator):
        is_const: bool = True

        for c in expr.get_operands():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const
            if c.type != types.BoolType(False):
                status = False
                log.error(
                    f"Invalid operands for '{expr.symbol}', found '{c.type}' ('{c}') but expected 'bool'\n\t{expr}",
                __name__,
                expr.loc
                )

        expr.type = types.BoolType(is_const)
    elif isinstance(expr, cpt.TemporalOperator):
        is_const: bool = True

        for c in expr.get_operands():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const
            if c.type != types.BoolType(False):
                status = False
                log.error(
                    f"Invalid operands for '{expr.symbol}', found '{c.type}' ('{c}') but expected 'bool'\n\t{expr}",
                __name__,
                expr.loc
                )

        # check for mixed-time formulas
        if isinstance(expr, cpt.FutureTimeOperator):
            if context.is_past_time():
                status = False
                log.error(
                    f"Mixed-time formulas unsupported, found FT formula in PTSPEC.\n\t{expr}",
                __name__,
                expr.loc
                )
        elif isinstance(expr, cpt.PastTimeOperator):
            if context.implementation != types.R2U2Implementation.C:
                status = False
                log.error(
                    f"Past-time operators only support in C version of R2U2.\n\t{expr}",
                __name__,
                expr.loc
                )
            if context.is_future_time():
                status = False
                log.error(
                    f"Mixed-time formulas unsupported, found PT formula in FTSPEC.\n\t{expr}",
                __name__,
                expr.loc
                )

        if expr.interval.lb > expr.interval.ub:
            status = False
            log.error(
                "Time interval invalid, lower bound must less than or equal to upper bound.\n\t"
                f"[{expr.interval.lb},{expr.interval.ub}]",
                __name__,
                expr.loc
            )

        expr.type = types.BoolType(is_const)
    elif isinstance(expr, cpt.SetExpression):
        t: types.Type = types.NoType()
        is_const: bool = True

        for m in expr.get_members():
            status = status and type_check_expr(m, context)
            is_const = is_const and m.type.is_const
            t = m.type

        for m in expr.get_members():
            if m.type != t:
                status = False
                log.error(
                    f"Set '{expr}' must be of homogeneous type (found '{m.type}' and '{t}')",
                __name__,
                expr.loc
                )

        expr.type = types.SetType(is_const, t)
    elif isinstance(expr, cpt.SetAggOperator):
        s: cpt.SetExpression = expr.get_set()
        boundvar: cpt.Variable = expr.get_boundvar()

        status = status and type_check_expr(s, context)

        if isinstance(s.type, types.SetType):
            context.add_variable(boundvar.symbol, s.type.member_type)
        else:
            status = False
            log.error(
                f"Set aggregation set must be Set type (found '{s.type}')",
                __name__,
                expr.loc
            )

        if (
            isinstance(expr, cpt.ForExactly)
            or isinstance(expr, cpt.ForAtLeast)
            or isinstance(expr, cpt.ForAtMost)
        ):
            if not context.booleanizer_enabled:
                status = False
                log.error(
                    "Parameterized set aggregation operators require Booleanizer, but Booleanizer not enabled.",
                __name__,
                expr.loc
                )

            n: cpt.Expression = expr.get_num()
            status = status and type_check_expr(n, context)
            if not types.is_integer_type(n.type):
                status = False
                log.error(
                    f"Parameter for set aggregation must be integer type (found '{n.type}')",
                __name__,
                expr.loc
                )

        e: cpt.Expression = expr.get_expr()
        status = status and type_check_expr(e, context)

        if e.type != types.BoolType(False):
            status = False
            log.error(
                f"Set aggregation expression must be 'bool' (found '{expr.type}')",
                __name__,
                expr.loc
            )

        expr.type = types.BoolType(expr.type.is_const and s.type.is_const)
    elif isinstance(expr, cpt.Struct):
        is_const: bool = True

        for member in expr.get_members():
            status = status and type_check_expr(member, context)
            is_const = is_const and member.type.is_const

        for m, t in context.structs[expr.symbol].items():
            member = expr.get_member(m)
            if not member:
                raise RuntimeError(f"Member '{m}' not in struct '{expr.symbol}'.")

            if member.type != t:
                log.error(
                    f"Member '{m}' invalid type for struct '{expr.symbol}' (expected '{t}' but got '{member.type}')",
                __name__,
                expr.loc
                )

        expr.type = types.StructType(is_const, expr.symbol)
    elif isinstance(expr, cpt.StructAccess):
        struct = expr.get_struct()
        status = status and type_check_expr(struct, context)

        struct_symbol = expr.get_struct().type.name
        if struct_symbol not in context.structs:
            log.error(
                f"Struct '{struct_symbol}' not defined ({expr}).",
                __name__,
                expr.loc
            )
            status = False

        valid_member: bool = False
        for m, t in context.structs[struct_symbol].items():
            if expr.member == m:
                expr.type = t
                valid_member = True

        if not valid_member:
            status = False
            log.error(
                f"Member '{expr.member}' invalid for struct '{struct_symbol}'",
                __name__,
                expr.loc
            )
    else:
        log.error(f"Invalid expression ({type(expr)})\n\t{expr}", __name__, expr.loc)
        status = False

    return status


def type_check_atomic(
    atomic: cpt.AtomicCheckerDefinition, context: cpt.Context
) -> bool:
    status = True

    relational_expr = atomic.get_expr()

    if not isinstance(relational_expr, cpt.RelationalOperator):
        log.error(
            f"Atomic checker definition not a relation.\n\t"
            f"{atomic}",
            __name__,
            relational_expr.loc
        )
        return False

    lhs = relational_expr.get_lhs()
    rhs = relational_expr.get_rhs()

    if isinstance(lhs, cpt.FunctionCall):
        if lhs.symbol not in context.atomic_checker_filters:
            log.error(
                f"Invalid atomic checker filter ('{lhs.symbol}')",
                __name__,
                lhs.loc
            )
            status = False

        if lhs.num_children() != len(context.atomic_checker_filters[lhs.symbol]):
            log.error(
                f"Atomic checker filter argument mismatch. Expected {len(context.atomic_checker_filters[lhs.symbol])} arguments, got {lhs.num_children()}",
                __name__,
                lhs.loc
            )
            status = False

        for arg, target_type in zip(
            lhs.get_operands(), context.atomic_checker_filters[lhs.symbol]
        ):
            if not isinstance(arg, cpt.Literal):
                log.error(
                    f"Atomic checker filter argument '{arg}' is not a signal nor constant.",
                __name__,
                arg.loc
                )
                status = False

            type_check_expr(arg, context)  # assigns signals their types

            if arg.type != target_type:
                log.error(
                    f"Atomic checker filter argument '{arg}' does not match expected type. Expected {target_type}, found {arg.type}.",
                __name__,
                arg.loc
                )
                status = False
    elif isinstance(lhs, cpt.Signal):
        type_check_expr(lhs, context)
    else:
        log.error(
            "Left-hand side of atomic checker definition not a filter nor signal.\n\t"
            f"{lhs}",
                __name__,
                lhs.loc
        )
        status = False

    if not isinstance(rhs, cpt.Literal):
        log.error(
            "Right-hand side of atomic checker definition not a constant or signal.\n\t"
            f"{rhs}",
                __name__,
                rhs.loc
        )
        status = False

    return status


def type_check_section(section: cpt.C2POSection, context: cpt.Context) -> bool:
    status = True

    if isinstance(section, cpt.InputSection):
        for declaration in section.get_signals():
            for signal in declaration.get_symbols():
                if signal in context.get_symbols():
                    status = False
                    log.error(
                        f"Symbol '{signal}' already in use.",
                        __name__,
                        declaration.loc
                    )

                context.add_signal(signal, declaration.get_type())
    elif isinstance(section, cpt.DefineSection):
        for definition in section.get_definitions():
            if definition.symbol in context.get_symbols():
                status = False
                log.error(
                    f"Symbol '{definition.symbol}' already in use.",
                    __name__,
                    definition.loc
                )

            status = status and type_check_expr(definition.get_expr(), context)
            if status:
                context.add_definition(definition.symbol, definition.get_expr())
    elif isinstance(section, cpt.StructSection):
        for struct in section.get_structs():
            if struct.symbol in context.get_symbols():
                status = False
                log.error(
                    f"Symbol '{struct.symbol}' already in use.",
                    __name__,
                    struct.loc
                )

            context.add_struct(struct.symbol, struct.get_members())
    elif isinstance(section, cpt.AtomicSection):
        for atomic in section.get_atomic_checkers():
            if atomic.symbol in context.get_symbols():
                status = False
                log.error(
                    f"Symbol '{atomic.symbol}' already in use.",
                    __name__,
                    atomic.loc
                )

            status = status and type_check_atomic(atomic, context)
            if status:
                context.add_atomic(atomic.symbol, atomic.get_expr())
    elif isinstance(section, cpt.SpecSection):
        if isinstance(section, cpt.FutureTimeSpecSection):
            if context.has_future_time:
                log.error("Only one FTSPEC section allowed.", __name__, section.loc)
                status = False
            context.has_future_time = True
            context.set_future_time()
        else:
            if context.has_past_time:
                log.error("Only one PTSPEC section allowed.", __name__, section.loc)
                status = False
            context.has_past_time = True
            context.set_past_time()

        for spec in section.get_specs():
            if spec.symbol != "" and spec.symbol in context.get_symbols():
                status = False
                log.error(f"Symbol '{spec.symbol}' already in use.", __name__, spec.loc)

            if isinstance(spec, cpt.Specification):
                status = status and type_check_expr(spec, context)
                if status:
                    context.add_specification(spec.symbol, spec)
            elif isinstance(spec, cpt.Contract):
                status = status and type_check_expr(spec.get_assumption(), context)
                status = status and type_check_expr(spec.get_guarantee(), context)
                if status:
                    context.add_contract(spec.symbol, spec)

    return status


def type_check(
    program: cpt.Program,
    impl: types.R2U2Implementation,
    mission_time: int,
    atomic_checkers: bool,
    booleanizer: bool,
    assembly_enabled: bool,
    signal_mapping: types.SignalMapping,
) -> tuple[bool, cpt.Context]:
    status: bool = True
    context = cpt.Context(
        impl,
        mission_time,
        atomic_checkers,
        booleanizer,
        assembly_enabled,
        signal_mapping,
    )

    for section in program.get_sections():
        status = status and type_check_section(section, context)

    return (status, context)
