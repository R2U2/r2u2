from __future__ import annotations

from typing import cast

from c2po import cpt, log, types, options

MODULE_CODE = "TYPC"


def type_check_expr(start: cpt.Expression, context: cpt.Context) -> bool:
    """Returns True `start` is well-typed."""
    for expr in cpt.postorder(start, context):
        if isinstance(expr, cpt.Formula):
            if not types.is_bool_type(expr.get_expr().type):
                log.error(
                    MODULE_CODE,
                    f"Formula must be a bool, found {expr.get_expr().type}",
                    expr.loc,
                )
                return False

            context.add_formula(expr.symbol, expr)

            expr.type = types.BoolType()
        elif isinstance(expr, cpt.Contract):
            if not types.is_bool_type(expr.children[0].type):
                log.error(
                    MODULE_CODE,
                    f"Assume of AGC must be a bool, found {expr.children[0].type}",
                    expr.loc,
                )
                return False

            if not types.is_bool_type(expr.children[1].type):
                log.error(
                    MODULE_CODE,
                    f"Guarantee of AGC must be a bool, found {expr.children[1].type}",
                    expr.loc,
                )
                return False

            context.add_contract(expr.symbol, expr)

            expr.type = types.ContractValueType()
        elif isinstance(expr, cpt.Constant):
            if (
                isinstance(expr.value, int)
                and expr.value.bit_length() > types.IntType.width
            ):
                log.error(
                    MODULE_CODE,
                    f"Constant '{expr.value}' not representable in configured int width ('{types.IntType.width}')",
                    expr.loc,
                )
                return False

            # TODO: Implement a check for valid float width, maybe with something like:
            # if len(value.hex()[2:]) > types.FloatType.width:
            #     ...
        elif isinstance(expr, cpt.Signal):
            if (
                context.options.assembly_enabled
                and expr.symbol not in context.options.signal_mapping
            ):
                log.error(
                    MODULE_CODE,
                    f"Mapping does not contain signal '{expr.symbol}'",
                    expr.loc,
                )
                return False
            
            if (
                context.options.frontend is not types.R2U2Engine.BOOLEANIZER
                and expr.type in {types.IntType(), types.FloatType()}
            ):
                log.error(
                    MODULE_CODE,
                    f"Non-bool type found '{expr.symbol}' ({expr.type})\n\t"
                    f"Did you mean to enable the Booleanizer?",
                    expr.loc,
                )
                return False

            if context.options.frontend is types.R2U2Engine.BOOLEANIZER:
                expr.engine = types.R2U2Engine.BOOLEANIZER

            if expr.symbol in context.options.signal_mapping:
                expr.signal_id = context.options.signal_mapping[expr.symbol]

            expr.type = context.signals[expr.symbol]
        elif isinstance(expr, cpt.Variable):
            symbol = expr.symbol

            if symbol in context.bound_vars:
                set_expr = context.bound_vars[symbol]
                if not types.is_array_type(set_expr.type):
                    log.internal(
                        MODULE_CODE,
                        f"Set aggregation set not assigned to type 'set', found '{set_expr.type}'\n\t"
                        f"{expr}",
                        expr.loc,
                    )
                    return False

                set_expr_type = cast(types.ArrayType, set_expr.type)
                expr.type = set_expr_type.member_type
            elif symbol in context.variables:
                expr.type = context.variables[symbol]
            elif symbol in context.definitions:
                expr.type = context.definitions[symbol].type
            elif symbol in context.structs:
                log.error(
                    MODULE_CODE,
                    "Defined structs may not be used as variables, try declaring the struct first",
                    expr.loc,
                )
                return False
            elif symbol in context.specifications:
                expr.type = types.BoolType()
            elif symbol in context.contracts:
                log.error(
                    MODULE_CODE,
                    f"Contracts not allowed as sub-expressions ('{symbol}')",
                    expr.loc,
                )
                return False
            else:
                log.error(MODULE_CODE, f"Symbol '{symbol}' not recognized", expr.loc)
                return False
        elif isinstance(expr, cpt.ArrayExpression):
            new_type: types.Type = types.NoType()
            is_const: bool = True

            for member in expr.children:
                is_const = is_const and member.type.is_const
                new_type = member.type

            for member in expr.children:
                if member.type != new_type:
                    log.error(
                        MODULE_CODE,
                        f"Set '{expr}' must be of homogeneous type (found '{member.type}' and '{new_type}')",
                        expr.loc,
                    )
                    return False

            expr.type = types.ArrayType(
                new_type, is_const=is_const, size=len(expr.children)
            )
        elif isinstance(expr, cpt.ArraySlice):
            array_type = expr.get_array().type
            if not isinstance(array_type, types.ArrayType):
                log.error(
                    MODULE_CODE,
                    f"Array access on a non-array expression ({expr})",
                    expr.loc,
                )
                return False

            if (abs(expr.start) > array_type.size or abs(expr.stop) > array_type.size) and array_type.size > -1:
                log.error(MODULE_CODE, f"Out-of-bounds array index ({expr})", expr.loc)
                return False

            if expr.start < 0:
                expr.start = -expr.start
            if expr.stop < 0:
                expr.stop = -expr.stop
            if expr.start > expr.stop:
                log.error(MODULE_CODE, f"Invalid array index ({expr}), {expr.start} is greater than {expr.stop}", expr.loc)
                return False

            expr.type = types.ArrayType(
                array_type.member_type, is_const=expr.get_array().type.is_const, size=expr.stop - expr.start + 1
            )
        elif isinstance(expr, cpt.ArrayIndex):
            array_type = expr.get_array().type
            if not isinstance(array_type, types.ArrayType):
                log.error(
                    MODULE_CODE,
                    f"Array access on a non-array expression ({expr})",
                    expr.loc,
                )
                return False

            if abs(expr.index) > array_type.size and array_type.size > -1:
                log.error(MODULE_CODE, f"Out-of-bounds array index ({expr})", expr.loc)
                return False

            if expr.index < 0:
                expr.index = -expr.index

            # Hacky special case where the array is a signal array, we use a temporary signal to
            # avoid repeating code
            if isinstance(expr.get_array(), cpt.Variable):
                tmp_signal = cpt.Signal(expr.loc, str(expr), array_type.member_type)
                context.signals[str(expr)] = types.NoType()
                status = type_check_expr(tmp_signal, context)
                del context.signals[str(expr)]
                if not status:
                    return False

            expr.type = array_type.member_type
        elif isinstance(expr, cpt.StructAccess):
            struct_symbol = expr.get_struct().type.symbol
            if struct_symbol not in context.structs:
                log.error(
                    MODULE_CODE,
                    f"Struct '{struct_symbol}' not defined ({expr})",
                    expr.loc,
                )
                return False

            valid_member: bool = False
            for member, new_type in context.structs[struct_symbol].items():
                if expr.member == member:
                    expr.type = new_type
                    valid_member = True

            if not valid_member:
                log.error(
                    MODULE_CODE,
                    f"Member '{expr.member}' invalid for struct '{struct_symbol}'",
                    expr.loc,
                )
                return False
        elif isinstance(expr, cpt.FunctionCall):
            # For now, this can only be a struct instantiation
            if expr.symbol not in context.structs:
                log.error(
                    MODULE_CODE,
                    f"General functions unsupported\n\t{expr}",
                    expr.loc,
                )
                return False
            
            target_types = [m for m in context.structs[expr.symbol].values()]
            actual_types = [c.type for c in expr.children]

            if any(
                [
                    target_type != actual_type
                    for target_type, actual_type in zip(target_types, actual_types)
                ]
            ):
                log.error(
                    MODULE_CODE,
                    f"Struct instantiation/function call does not match signature."
                    f"\n\tFound:    {expr.symbol}({', '.join([str(t) for t in actual_types])})"
                    f"\n\tExpected: {expr.symbol}({', '.join([str(t) for t in target_types])})",
                    expr.loc,
                )
                return False

            is_const = False
            if all([child.type.is_const for child in expr.children]):
                is_const = True

            expr.type = types.StructType(expr.symbol, is_const)
        elif isinstance(expr, cpt.SetAggregation):
            s: cpt.ArrayExpression = expr.get_set()
            boundvar: cpt.Variable = expr.bound_var

            if isinstance(s.type, types.ArrayType):
                context.add_variable(boundvar.symbol, s.type.member_type)
            else:
                log.error(
                    MODULE_CODE,
                    f"Set aggregation set must be Set type (found '{s.type}')",
                    expr.loc,
                )
                return False

            if expr.operator in {
                cpt.SetAggregationKind.FOR_EXACTLY,
                cpt.SetAggregationKind.FOR_AT_MOST,
                cpt.SetAggregationKind.FOR_AT_LEAST,
            }:
                if context.options.frontend is not types.R2U2Engine.BOOLEANIZER:
                    log.error(
                        MODULE_CODE,
                        "Parameterized set aggregation operators require Booleanizer, but Booleanizer not enabled",
                        expr.loc,
                    )
                    return False

                n = cast(cpt.Expression, expr.get_num())
                if not types.is_integer_type(n.type):
                    log.error(
                        MODULE_CODE,
                        f"Parameter for set aggregation must be integer type (found '{n.type}')",
                        expr.loc,
                    )
                    return False

            e: cpt.Expression = expr.get_expr()

            if e.type != types.BoolType():
                log.error(
                    MODULE_CODE,
                    f"Set aggregation expression must be 'bool' (found '{expr.type}')",
                    expr.loc,
                )
                return False

            expr.type = types.BoolType(expr.type.is_const and s.type.is_const)
        elif isinstance(expr, cpt.TemporalOperator):
            is_const: bool = True

            for child in expr.children:
                is_const = is_const and child.type.is_const
                if child.type != types.BoolType():
                    log.error(
                        MODULE_CODE,
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'bool'\n\t{expr}",
                        expr.loc,
                    )
                    return False

            # check for mixed-time formulas
            if cpt.is_future_time_operator(expr):
                if context.is_past_time():
                    log.error(
                        MODULE_CODE,
                        f"Mixed-time formulas unsupported, found FT formula in PTSPEC\n\t{expr}",
                        expr.loc,
                    )
                    return False
            elif cpt.is_past_time_operator(expr):
                if (
                    context.options.impl != types.R2U2Implementation.C
                    and context.options.impl != types.R2U2Implementation.RUST
                ):
                    log.error(
                        MODULE_CODE,
                        f"Past-time operators only support in C version of R2U2\n\t{expr}",
                        expr.loc,
                    )
                    return False
                if context.is_future_time():
                    log.error(
                        MODULE_CODE,
                        f"Mixed-time formulas unsupported, found PT formula in FTSPEC\n\t{expr}",
                        expr.loc,
                    )
                    return False

            interval = expr.interval
            if not interval:
                log.internal(
                    MODULE_CODE,
                    "Interval not set for temporal operator\n\t" f"{expr}",
                    expr.loc,
                )
                return False

            if interval.lb > interval.ub:
                log.error(
                    MODULE_CODE,
                    "Time interval invalid, lower bound must less than or equal to upper bound\n\t"
                    f"[{interval.lb},{interval.ub}]",
                    expr.loc,
                )
                return False

            expr.type = types.BoolType(is_const)
        elif cpt.is_bitwise_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const: bool = True

            if (
                context.options.impl != types.R2U2Implementation.C
                and context.options.impl != types.R2U2Implementation.RUST
            ):
                log.error(
                    MODULE_CODE,
                    f"Bitwise operators only support in C version of R2U2.\n\t{expr}",
                    expr.loc,
                )
                return False

            if context.options.frontend is not types.R2U2Engine.BOOLEANIZER:
                log.error(
                    MODULE_CODE,
                    f"Found context.booleanizer_enabled expression, but Booleanizer expressions disabled\n\t{expr}",
                    expr.loc,
                )
                return False

            new_type: types.Type = expr.children[0].type

            if all([c.type.is_const for c in expr.children]):
                new_type.is_const = True

            for child in expr.children:
                if isinstance(child, cpt.ArrayExpression) or isinstance(child, cpt.ArraySlice):
                    log.error(
                        MODULE_CODE,
                        f"Bitwise operators not supported on arrays \n\t{expr}",
                        expr.loc,
                    )
                    return False
                elif child.type != new_type or not types.is_integer_type(child.type):
                    log.error(
                        MODULE_CODE,
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected '{new_type}'\n\t{expr}",
                        expr.loc,
                    )
                    return False

            expr.type = new_type
        elif cpt.is_arithmetic_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const: bool = True

            if (
                context.options.impl != types.R2U2Implementation.C
                and context.options.impl != types.R2U2Implementation.RUST
            ):
                log.error(
                    MODULE_CODE,
                    f"Arithmetic operators only support in C version of R2U2\n\t{expr}",
                    expr.loc,
                )
                return False

            if context.options.frontend is not types.R2U2Engine.BOOLEANIZER:
                log.error(
                    MODULE_CODE,
                    f"Found Booleanizer expression, but Booleanizer expressions disabled\n\t{expr}",
                    expr.loc,
                )
                return False

            new_type: types.Type = expr.children[0].type

            if all([c.type.is_const for c in expr.children]):
                new_type.is_const = True

            if expr.operator is cpt.OperatorKind.ARITHMETIC_DIVIDE:
                rhs: cpt.Expression = expr.children[1]
                # TODO: disallow division by non-const expression entirely
                if isinstance(rhs, cpt.Constant) and rhs.value == 0:
                    log.error(
                        MODULE_CODE,
                        f"Divide by zero found\n\t{expr}",
                        expr.loc,
                    )
                    return False
                
            if expr.operator is cpt.OperatorKind.ARITHMETIC_SQRT:
                rhs: cpt.Expression = expr.children[0]
                if rhs.type == types.IntType():
                    log.error(
                        MODULE_CODE,
                        f"Square root invalid for integer expressions ({rhs}).\n\t{expr}",
                        expr.loc,
                    )
                    return False
            
            if expr.operator is cpt.OperatorKind.ARITHMETIC_POWER:
                lhs: cpt.Expression = expr.children[0]
                rhs: cpt.Expression = expr.children[1]
                if lhs.type == types.IntType():
                    if isinstance(rhs, cpt.Constant):
                        if rhs.value < 0:
                            log.error(
                                MODULE_CODE,
                                f"Power function invalid for integer expressions with negative exponents ({rhs}).\n\t{expr}",
                                expr.loc,
                            )
                            return False
                    else:
                        log.error(
                            MODULE_CODE,
                            f"Power function invalid for integer expressions with possible negative integer exponents ({rhs}).\n\t{expr}",
                            expr.loc,
                        )
                        return False

            for child in expr.children:
                if isinstance(child, cpt.ArrayExpression) or isinstance(child, cpt.ArraySlice):
                    log.error(
                        MODULE_CODE,
                        f"Arithmetic operators not supported on arrays \n\t{expr}",
                        expr.loc,
                    )
                    return False
                elif child.type != new_type:
                    log.error(
                        MODULE_CODE,
                        f"Operand of '{expr}' must be of homogeneous type\n\t"
                        f"Found {child.type} and {new_type}",
                        expr.loc,
                    )
                    return False

            expr.type = new_type
        elif cpt.is_relational_operator(expr):
            expr = cast(cpt.Operator, expr)
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]

            if context.options.impl != types.R2U2Implementation.C:
                log.error(
                    MODULE_CODE,
                    f"Arithmetic operators only support in C version of R2U2\n\t{expr}",
                    expr.loc,
                )
                return False

            if context.options.frontend not in {
                types.R2U2Engine.BOOLEANIZER,
            } and expr.operator not in {
                cpt.OperatorKind.EQUAL,
                cpt.OperatorKind.NOT_EQUAL,
            }:
                log.error(
                    MODULE_CODE,
                    f"Found Booleanizer expression, but Booleanizer expressions disabled\n\t{expr}",
                    expr.loc,
                )
                return False

            if lhs.type != rhs.type:
                log.error(
                    MODULE_CODE,
                    f"Invalid operands for '{expr.symbol}', must be of same type (found '{lhs.type}' and '{rhs.type}')\n\t{expr}",
                    expr.loc,
                )
                return False

            expr.type = types.BoolType(lhs.type.is_const and rhs.type.is_const)
        elif cpt.is_logical_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const: bool = True

            for child in expr.children:
                is_const = is_const and child.type.is_const
                if child.type != types.BoolType():
                    log.error(
                        MODULE_CODE,
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'bool'\n\t{expr}",
                        expr.loc,
                    )
                    return False

            expr.type = types.BoolType(is_const)
        elif cpt.is_prev_operator(expr):
            for child in expr.get_descendants():
                if cpt.is_prev_operator(child):
                    log.error(
                        f"Invalid nested previous statements, ({child}).\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False
            expr.type = expr.children[0].type

        else:
            log.error(
                MODULE_CODE,
                f"Invalid expression ({type(expr)})\n\t{expr}",
                expr.loc,
            )
            return False

    return True


def type_check_section(section: cpt.ProgramSection, context: cpt.Context) -> bool:
    status = True

    if isinstance(section, cpt.InputSection):
        for declaration in section.signal_decls:
            for signal in declaration.variables:
                if signal in context.get_symbols():
                    status = False
                    log.error(
                        MODULE_CODE,
                        f"Symbol '{signal}' already in use",
                        declaration.loc,
                    )

                context.add_signal(signal, declaration.type)

                if not isinstance(declaration.type, types.ArrayType):
                    continue

                signals = [
                    cpt.Signal(
                        declaration.loc, f"{signal}[{i}]", declaration.type.member_type
                    )
                    for i in range(0, declaration.type.size)
                ]
                signal_array = cpt.ArrayExpression(
                    declaration.loc, cast("list[cpt.Expression]", signals)
                )
                signal_array.type = declaration.type
                context.add_definition(signal, signal_array)
                [
                    context.add_signal(f"{signal}[{i}]", declaration.type.member_type)
                    for i in range(0, declaration.type.size)
                ]
                [type_check_expr(sig, context) for sig in signals]
    elif isinstance(section, cpt.DefineSection):
        for definition in section.defines:
            if definition.symbol in context.get_symbols():
                status = False
                log.error(
                    MODULE_CODE,
                    f"Symbol '{definition.symbol}' already in use",
                    definition.loc,
                )

            is_good_def = type_check_expr(definition.expr, context)

            if is_good_def:
                context.add_definition(definition.symbol, definition.expr)

            status = status and is_good_def
    elif isinstance(section, cpt.StructSection):
        for struct in section.struct_defs:
            if struct.symbol in context.get_symbols():
                status = False
                log.error(
                    MODULE_CODE,
                    f"Symbol '{struct.symbol}' already in use",
                    struct.loc,
                )

            context.add_struct(struct.symbol, struct.members)
    elif isinstance(section, cpt.SpecSection):
        if isinstance(section, cpt.FutureTimeSpecSection):
            context.set_future_time()
        else:
            context.set_past_time()

        for spec in section.specs:
            if spec.symbol != "" and spec.symbol in context.get_symbols():
                status = False
                log.error(
                    MODULE_CODE,
                    f"Symbol '{spec.symbol}' already in use",
                    spec.loc,
                )

            is_good_spec = type_check_expr(spec, context)
            status = status and is_good_spec

    return status


def type_check(program: cpt.Program, opts: options.Options) -> tuple[bool, cpt.Context]:
    log.debug(MODULE_CODE, 1, "Type checking")

    status: bool = True
    context = cpt.Context(opts)

    for section in program.sections:
        status = type_check_section(section, context) and status

    return (status, context)
