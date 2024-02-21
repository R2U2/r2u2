from __future__ import annotations

from typing import cast

from c2po import cpt, log, types

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
            if isinstance(expr.value, int) and expr.value.bit_length() > types.IntType.width:
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
            if context.assembly_enabled and expr.symbol not in context.signal_mapping:
                log.error(
                    MODULE_CODE,
                    f"Mapping does not contain signal '{expr.symbol}'",
                    expr.loc,
                )
                return False
            
            if context.frontend is types.R2U2Engine.BOOLEANIZER:
                expr.engine = types.R2U2Engine.BOOLEANIZER

            if expr.symbol in context.signal_mapping:
                expr.signal_id = context.signal_mapping[expr.symbol]

            expr.type = context.signals[expr.symbol]
        elif isinstance(expr, cpt.AtomicChecker):
            if context.frontend is not types.R2U2Engine.ATOMIC_CHECKER:
                log.error(
                    MODULE_CODE,
                    "Atomic checkers not enabled, but found in expression\n\t"
                    f"{expr}",
                    expr.loc,
                )
                return False

            if expr.symbol not in context.atomic_checkers:
                log.error(
                    MODULE_CODE,
                    f"Atomic checker '{expr.symbol}' not defined",
                    expr.loc,
                )
                return False
        elif isinstance(expr, cpt.Variable):
            symbol = expr.symbol

            if symbol in context.bound_vars:
                set_expr = context.bound_vars[symbol]
                if not types.is_set_type(set_expr.type):
                    log.internal(
                        MODULE_CODE,
                        f"Set aggregation set not assigned to type 'set', found '{set_expr.type}'\n\t"
                        f"{expr}",
                            expr.loc,
                    )
                    return False

                set_expr_type = cast(types.SetType, set_expr.type)
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
            elif symbol in context.atomic_checkers:
                expr.type = types.BoolType()
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
                log.error(
                    MODULE_CODE, f"Symbol '{symbol}' not recognized", expr.loc
                )
                return False
        elif isinstance(expr, cpt.SetExpression):
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

            expr.type = types.SetType(new_type, is_const)
        elif isinstance(expr, cpt.Struct):
            is_const: bool = True

            for member in expr.children:
                is_const = is_const and member.type.is_const

            for member, new_type in context.structs[expr.symbol].items():
                member = expr.get_member(member)
                if not member:
                    raise RuntimeError(
                        f"Member '{member}' not in struct '{expr.symbol}'"
                    )

                if member.type != new_type:
                    log.error(
                        MODULE_CODE,
                        f"Member '{member}' invalid type for struct '{expr.symbol}' (expected '{new_type}' but got '{member.type}')",
                        expr.loc,
                    )

            expr.type = types.StructType(expr.symbol, is_const)
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

            is_const = False
            if all([child.type.is_const for child in expr.children]):
                is_const = True

            expr.type = types.StructType(expr.symbol, is_const)
        elif isinstance(expr, cpt.SetAggregation):
            s: cpt.SetExpression = expr.get_set()
            boundvar: cpt.Variable = expr.bound_var

            if isinstance(s.type, types.SetType):
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
                if context.frontend is not types.R2U2Engine.BOOLEANIZER:
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
                if context.implementation != types.R2U2Implementation.C:
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

            if context.implementation != types.R2U2Implementation.C:
                log.error(
                    MODULE_CODE,
                    f"Bitwise operators only support in C version of R2U2.\n\t{expr}",
                    expr.loc,
                )
                return False

            if context.frontend is not types.R2U2Engine.BOOLEANIZER:
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
                if child.type != new_type or not types.is_integer_type(child.type):
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

            if context.implementation != types.R2U2Implementation.C:
                log.error(
                    MODULE_CODE,
                    f"Arithmetic operators only support in C version of R2U2\n\t{expr}",
                    expr.loc,
                )
                return False

            if context.frontend is not types.R2U2Engine.BOOLEANIZER:
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

            for child in expr.children:
                if child.type != new_type:
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

            if lhs.type != rhs.type:
                log.error(
                    MODULE_CODE,
                    f"Invalid operands for '{expr.symbol}', must be of same type (found '{lhs.type}' and '{rhs.type}')\n\t{expr}",
                    expr.loc,
                )
                return False
            
            if expr.operator in {
                cpt.OperatorKind.EQUAL,
                cpt.OperatorKind.NOT_EQUAL,
            }:
                if lhs.type == types.FloatType():
                    log.error(
                        MODULE_CODE,
                        f"Equality invalid for float expressions ({lhs}).\n\t{expr}",
                        expr.loc,
                    )
                    return False
                if rhs.type == types.FloatType():
                    log.error(
                        MODULE_CODE,
                        f"Equality invalid for float expressions ({rhs}).\n\t{expr}",
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
        else:
            log.error(
                MODULE_CODE,
                f"Invalid expression ({type(expr)})\n\t{expr}",
                expr.loc,
            )
            return False

    return True


def type_check_atomic(
    atomic: cpt.AtomicCheckerDefinition, context: cpt.Context
) -> bool:
    relational_expr = atomic.get_expr()

    if not cpt.is_relational_operator(relational_expr):
        log.error(
            MODULE_CODE,
            f"Atomic checker definition not a relation\n\t" f"{atomic}",
            relational_expr.loc,
        )
        return False

    if not type_check_expr(relational_expr, context):
        return False

    lhs = relational_expr.children[0]
    rhs = relational_expr.children[1]

    if isinstance(lhs, cpt.FunctionCall):
        log.error(
            MODULE_CODE,
            "Atomic checker filters unsupported",
            lhs.loc,
        )
        return False
    elif not isinstance(lhs, cpt.Signal):
        log.error(
            MODULE_CODE,
            "Left-hand side of atomic checker definition not a filter nor signal\n\t"
            f"{atomic}",
            lhs.loc,
        )
        return False

    if not isinstance(rhs, (cpt.Constant, cpt.Signal)):
        log.error(
            MODULE_CODE,
            "Right-hand side of atomic checker definition not a constant nor signal\n\t"
            f"{rhs}",
            rhs.loc,
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
    elif isinstance(section, cpt.AtomicSection):
        for atomic in section.atomics:
            if atomic.symbol in context.get_symbols():
                status = False
                log.error(
                    MODULE_CODE,
                    f"Symbol '{atomic.symbol}' already in use",
                    atomic.loc,
                )

            is_good_atomic = type_check_atomic(atomic, context)

            if is_good_atomic:
                context.add_atomic(atomic.symbol, atomic.get_expr())

            status = status and is_good_atomic
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


def type_check(
    program: cpt.Program,
    impl: types.R2U2Implementation,
    mission_time: int,
    frontend: types.R2U2Engine,
    assembly_enabled: bool,
    signal_mapping: types.SignalMapping,
) -> tuple[bool, cpt.Context]:
    log.debug(MODULE_CODE, 1, "Type checking")

    status: bool = True
    context = cpt.Context(
        impl,
        mission_time,
        frontend,
        assembly_enabled,
        signal_mapping,
    )

    for section in program.sections:
        status = type_check_section(section, context) and status

    return (status, context)
