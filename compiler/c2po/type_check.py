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
                    f"Formula must be a bool, found {expr.get_expr().type}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False
            
            if expr.get_expr().type.is_const:
                log.error(
                    f"Constant specification detected, remove or make this non-constant\n\t{expr}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            context.add_formula(expr.symbol, expr)

            expr.type = types.BoolType()
        elif isinstance(expr, cpt.Contract):
            if not types.is_bool_type(expr.children[0].type):
                log.error(
                    f"Assume of AGC must be a bool, found {expr.children[0].type}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            if not types.is_bool_type(expr.children[1].type):
                log.error(
                    f"Guarantee of AGC must be a bool, found {expr.children[1].type}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            context.add_contract(expr.symbol, expr)

            expr.type = types.ContractValueType()
        elif isinstance(expr, cpt.Constant):
            if isinstance(expr.value, int) and expr.value.bit_length() > types.IntType.width:
                log.error(
                    f"Constant '{expr.value}' not representable in configured int width ('{types.IntType.width}')",
                    module=MODULE_CODE,
                    location=expr.loc,
                )
                return False
            
            # TODO: Implement a check for valid float width, maybe with something like:
            # if len(value.hex()[2:]) > types.FloatType.width:
            #     ...
        elif isinstance(expr, cpt.Signal):
            if context.assembly_enabled and expr.symbol not in context.signal_mapping:
                log.error(
                    f"Mapping does not contain signal '{expr.symbol}'",
                    MODULE_CODE,
                    location=expr.loc,
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
                    "Atomic checkers not enabled, but found in expression\n\t"
                    f"{expr}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            if expr.symbol not in context.atomic_checkers:
                log.error(
                    f"Atomic checker '{expr.symbol}' not defined",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False
        elif isinstance(expr, cpt.Variable):
            symbol = expr.symbol

            if symbol in context.bound_vars:
                set_expr = context.bound_vars[symbol]
                if not types.is_set_type(set_expr.type):
                    log.internal(
                        f"Set aggregation set not assigned to type 'set', found '{set_expr.type}'\n\t"
                        f"{expr}",
                        MODULE_CODE,
                        location=expr.loc,
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
                    "Defined structs may not be used as variables, try declaring the struct first",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False
            elif symbol in context.atomic_checkers:
                expr.type = types.BoolType()
            elif symbol in context.specifications:
                expr.type = types.BoolType()
            elif symbol in context.contracts:
                log.error(
                    f"Contracts not allowed as sub-expressions ('{symbol}')",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False
            else:
                log.error(
                    f"Symbol '{symbol}' not recognized", MODULE_CODE, location=expr.loc
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
                        f"Set '{expr}' must be of homogeneous type (found '{member.type}' and '{new_type}')",
                        MODULE_CODE,
                        location=expr.loc,
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
                        f"Member '{member}' invalid type for struct '{expr.symbol}' (expected '{new_type}' but got '{member.type}')",
                        MODULE_CODE,
                        location=expr.loc,
                    )

            expr.type = types.StructType(expr.symbol, is_const)
        elif isinstance(expr, cpt.StructAccess):
            struct_symbol = expr.get_struct().type.symbol
            if struct_symbol not in context.structs:
                log.error(
                    f"Struct '{struct_symbol}' not defined ({expr})",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            valid_member: bool = False
            for member, new_type in context.structs[struct_symbol].items():
                if expr.member == member:
                    expr.type = new_type
                    valid_member = True

            if not valid_member:
                log.error(
                    f"Member '{expr.member}' invalid for struct '{struct_symbol}'",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False
        elif isinstance(expr, cpt.FunctionCall):
            # For now, this can only be a struct instantiation
            if expr.symbol not in context.structs:
                log.error(
                    f"General functions unsupported\n\t{expr}",
                    MODULE_CODE,
                    location=expr.loc,
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
                    f"Set aggregation set must be Set type (found '{s.type}')",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            if expr.operator in {
                cpt.SetAggregationKind.FOR_EXACTLY,
                cpt.SetAggregationKind.FOR_AT_MOST,
                cpt.SetAggregationKind.FOR_AT_LEAST,
            }:
                if context.frontend is not types.R2U2Engine.BOOLEANIZER:
                    log.error(
                        "Parameterized set aggregation operators require Booleanizer, but Booleanizer not enabled",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

                n = cast(cpt.Expression, expr.get_num())
                if not types.is_integer_type(n.type):
                    log.error(
                        f"Parameter for set aggregation must be integer type (found '{n.type}')",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

            e: cpt.Expression = expr.get_expr()

            if e.type != types.BoolType():
                log.error(
                    f"Set aggregation expression must be 'bool' (found '{expr.type}')",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            expr.type = types.BoolType(expr.type.is_const and s.type.is_const)
        elif isinstance(expr, cpt.TemporalOperator):
            is_const: bool = True

            for child in expr.children:
                is_const = is_const and child.type.is_const
                if child.type != types.BoolType():
                    log.error(
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'bool'\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

            # check for mixed-time formulas
            if cpt.is_future_time_operator(expr):
                if context.is_past_time():
                    log.error(
                        f"Mixed-time formulas unsupported, found FT formula in PTSPEC\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False
            elif cpt.is_past_time_operator(expr):
                if context.implementation != types.R2U2Implementation.C:
                    log.error(
                        f"Past-time operators only support in C version of R2U2\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False
                if context.is_future_time():
                    log.error(
                        f"Mixed-time formulas unsupported, found PT formula in FTSPEC\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

            interval = expr.interval
            if not interval:
                log.internal(
                    "Interval not set for temporal operator\n\t" f"{expr}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            if interval.lb > interval.ub:
                log.error(
                    "Time interval invalid, lower bound must less than or equal to upper bound\n\t"
                    f"[{interval.lb},{interval.ub}]",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            expr.type = types.BoolType(is_const)
        elif cpt.is_bitwise_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const: bool = True

            if context.implementation != types.R2U2Implementation.C:
                log.error(
                    f"Bitwise operators only support in C version of R2U2.\n\t{expr}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            if context.frontend is not types.R2U2Engine.BOOLEANIZER:
                log.error(
                    f"Found context.booleanizer_enabled expression, but Booleanizer expressions disabled\n\t{expr}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            new_type: types.Type = expr.children[0].type

            if all([c.type.is_const for c in expr.children]):
                new_type.is_const = True

            for child in expr.children:
                if child.type != new_type or not types.is_integer_type(child.type):
                    log.error(
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected '{new_type}'\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

            expr.type = new_type
        elif cpt.is_arithmetic_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const: bool = True

            if context.implementation != types.R2U2Implementation.C:
                log.error(
                    f"Arithmetic operators only support in C version of R2U2\n\t{expr}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False

            if context.frontend is not types.R2U2Engine.BOOLEANIZER:
                log.error(
                    f"Found Booleanizer expression, but Booleanizer expressions disabled\n\t{expr}",
                    MODULE_CODE,
                    location=expr.loc,
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
                        f"Divide by zero found\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

            for child in expr.children:
                if child.type != new_type:
                    log.error(
                        f"Operand of '{expr}' must be of homogeneous type\n\t"
                        f"Found {child.type} and {new_type}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

            expr.type = new_type
        elif cpt.is_relational_operator(expr):
            expr = cast(cpt.Operator, expr)
            lhs: cpt.Expression = expr.children[0]
            rhs: cpt.Expression = expr.children[1]

            if lhs.type != rhs.type:
                log.error(
                    f"Invalid operands for '{expr.symbol}', must be of same type (found '{lhs.type}' and '{rhs.type}')\n\t{expr}",
                    MODULE_CODE,
                    location=expr.loc,
                )
                return False
            
            if expr.operator in {
                cpt.OperatorKind.EQUAL,
                cpt.OperatorKind.NOT_EQUAL,
            }:
                if lhs.type == types.FloatType():
                    log.error(
                        f"Equality invalid for float expressions ({lhs}).\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False
                if rhs.type == types.FloatType():
                    log.error(
                        f"Equality invalid for float expressions ({rhs}).\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
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
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'bool'\n\t{expr}",
                        MODULE_CODE,
                        location=expr.loc,
                    )
                    return False

            expr.type = types.BoolType(is_const)
        else:
            log.error(
                f"Invalid expression ({type(expr)})\n\t{expr}",
                MODULE_CODE,
                location=expr.loc,
            )
            return False

    return True


def type_check_atomic(
    atomic: cpt.AtomicCheckerDefinition, context: cpt.Context
) -> bool:
    relational_expr = atomic.get_expr()

    if not cpt.is_relational_operator(relational_expr):
        log.error(
            f"Atomic checker definition not a relation\n\t" f"{atomic}",
            MODULE_CODE,
            location=relational_expr.loc,
        )
        return False

    if not type_check_expr(relational_expr, context):
        return False

    lhs = relational_expr.children[0]
    rhs = relational_expr.children[1]

    if isinstance(lhs, cpt.FunctionCall):
        log.error(
            "Atomic checker filters unsupported",
            MODULE_CODE,
            location=lhs.loc,
        )
        return False
    elif not isinstance(lhs, cpt.Signal):
        log.error(
            "Left-hand side of atomic checker definition not a filter nor signal\n\t"
            f"{atomic}",
            MODULE_CODE,
            location=lhs.loc,
        )
        return False

    if not isinstance(rhs, (cpt.Constant, cpt.Signal)):
        log.error(
            "Right-hand side of atomic checker definition not a constant nor signal\n\t"
            f"{rhs}",
            MODULE_CODE,
            location=rhs.loc,
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
                        f"Symbol '{signal}' already in use",
                        MODULE_CODE,
                        location=declaration.loc,
                    )

                context.add_signal(signal, declaration.type)
    elif isinstance(section, cpt.DefineSection):
        for definition in section.defines:
            if definition.symbol in context.get_symbols():
                status = False
                log.error(
                    f"Symbol '{definition.symbol}' already in use",
                    MODULE_CODE,
                    location=definition.loc,
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
                    f"Symbol '{struct.symbol}' already in use",
                    MODULE_CODE,
                    location=struct.loc,
                )

            context.add_struct(struct.symbol, struct.members)
    elif isinstance(section, cpt.AtomicSection):
        for atomic in section.atomics:
            if atomic.symbol in context.get_symbols():
                status = False
                log.error(
                    f"Symbol '{atomic.symbol}' already in use",
                    MODULE_CODE,
                    location=atomic.loc,
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
                    f"Symbol '{spec.symbol}' already in use",
                    MODULE_CODE,
                    location=spec.loc,
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
    log.debug("Type checking", MODULE_CODE)

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
