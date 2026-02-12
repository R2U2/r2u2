from typing import cast, Any
from c2po import cpt, log, types, command


def type_check_expr(start: cpt.Expression, context: cpt.Context, options: dict[str, Any]) -> bool:
    """Returns True `start` is well-typed."""
    log.debug(2, f"type checking: {repr(start)}")

    for expr in cpt.postorder(start, context):
        if isinstance(expr, cpt.Formula):
            if not types.is_bool_type(expr.get_expr().type):
                log.error(
                    f"formula must be a bool, found '{expr.get_expr().type}'",
                    expr.loc,
                )
                return False
                
            context.add_formula(expr.symbol, expr)

            expr.type = types.BoolType()
        elif isinstance(expr, cpt.Contract):
            if not types.is_bool_type(expr.children[0].type):
                log.error(
                    f"assume of AGC must be a bool, found '{expr.children[0].type}'",
                    expr.loc,
                )
                return False

            if not types.is_bool_type(expr.children[1].type):
                log.error(
                    f"guarantee of AGC must be a bool, found '{expr.children[1].type}'",
                    expr.loc,
                )
                return False

            context.add_contract(expr.symbol, expr)

            expr.type = types.ContractValueType()
        elif isinstance(expr, cpt.Constant):
            if (
                isinstance(expr.value, int)
                and expr.value.bit_length() > (types.IntType.width - (1 if types.IntType.is_signed else 0))
            ):
                log.error(
                    f"constant '{expr.value}' not representable in configured int type ({types.IntType.width} bits, {'signed' if types.IntType.is_signed else 'unsigned'})",
                    expr.loc,
                )
                return False

            # TODO: Implement a check for valid float width, maybe with something like:
            # if len(value.hex()[2:]) > types.FloatType.width:
            #     ...
        elif isinstance(expr, cpt.CurrentTimestamp):
            if types.IntType.is_signed:
                log.warning(
                    "int type is signed but TAU is unsigned",
                    expr.loc,
                )

            expr.type = types.IntType()
        elif isinstance(expr, cpt.Signal):
            if (
                not context.enable_booleanizer
                and (types.is_enum_type(context.signals[expr.symbol]) 
                    or context.signals[expr.symbol] in {types.IntType(), types.FloatType()})
            ):
                log.error(
                    f"non-bool type found '{expr.symbol}' ({context.signals[expr.symbol]})\n"
                    "    did you mean to enable the booleanizer?",
                    expr.loc,
                )
                return False

            if context.enable_booleanizer:
                expr.engine = types.R2U2Engine.BOOLEANIZER

            if expr.signal_id == -1 and expr.symbol in context.signal_mapping:
                expr.signal_id = context.signal_mapping[expr.symbol]

            expr.type = context.signals[expr.symbol]
        elif isinstance(expr, cpt.Variable):
            symbol = expr.symbol

            if symbol in context.bound_vars:
                set_expr = context.bound_vars[symbol]
                if not types.is_array_type(set_expr.type):
                    log.internal(
                        f"set aggregation set not assigned to type 'set', found '{set_expr.type}'\n    "
                        f"{expr}",
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
                    "defined structs may not be used as variables, try declaring the struct first\n    ",
                    expr.loc,
                )
                return False
            elif symbol in context.enums:
                log.error(
                    "Defined enums may not be used as variables, try utilizing the members of the enum",
                    expr.loc,
                )
                return False
            elif symbol in context.specifications:
                expr.type = types.BoolType()
            elif symbol in context.contracts:
                log.error(
                    f"contracts not allowed as sub-expressions ('{symbol}')",
                    expr.loc,
                )
                return False
            elif symbol in [name for enum in context.enums.values() for name in enum.keys()]:
                expr.type = types.EnumType(symbol)
            else:
                log.error(f"symbol '{symbol}' not recognized", expr.loc)
                return False
        elif isinstance(expr, cpt.Atomic):
            expr.type = types.BoolType()
        elif isinstance(expr, cpt.SymbolicIntervalVariable):
            expr.type = types.IntType(True)
        elif isinstance(expr, cpt.MissionTime):
            expr.type = types.IntType(True)
        elif isinstance(expr, cpt.ArrayExpression):
            new_type = types.NoType()
            is_const = True

            for member in expr.children:
                is_const = is_const and member.type.is_const
                new_type = member.type

            for member in expr.children:
                if member.type != new_type:
                    log.error(
                        f"set '{expr}' must be of homogeneous type (found '{member.type}' and '{new_type}')",
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
                    f"Array access on a non-array expression ({expr})",
                    expr.loc,
                )
                return False

            if (abs(expr.start) > array_type.size or abs(expr.stop) > array_type.size) and array_type.size > -1:
                log.error(f"Out-of-bounds array index ({expr})", expr.loc)
                return False

            if expr.start < 0:
                expr.start = -expr.start
            if expr.stop < 0:
                expr.stop = -expr.stop
            if expr.start > expr.stop:
                log.error(f"Invalid array index ({expr}), {expr.start} is greater than {expr.stop}", expr.loc)
                return False

            expr.type = types.ArrayType(
                array_type.member_type, is_const=expr.get_array().type.is_const, size=expr.stop - expr.start + 1
            )
        elif isinstance(expr, cpt.ArrayIndex):
            array_type = expr.get_array().type
            if not isinstance(array_type, types.ArrayType):
                log.error(
                    f"array access on a non-array expression ({expr})",
                    expr.loc,
                )
                return False

            if abs(expr.index) > array_type.size and array_type.size > -1:
                log.error(f"out-of-bounds array index ({expr})", expr.loc)
                return False

            if expr.index < 0:
                expr.index = -expr.index

            # Hacky special case where the array is a signal array, we use a temporary signal to
            # avoid repeating code
            if isinstance(expr.get_array(), cpt.Variable):
                tmp_signal = cpt.Signal(expr.loc, str(expr), array_type.member_type)
                context.signals[str(expr)] = types.NoType()
                status = type_check_expr(tmp_signal, context, options)
                del context.signals[str(expr)]
                if not status:
                    return False

            expr.type = array_type.member_type
        elif isinstance(expr, cpt.StructAccess):
            struct_symbol = expr.get_struct().type.symbol
            if struct_symbol not in context.structs:
                log.error(
                    f"struct '{struct_symbol}' not defined ({expr})",
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
                    f"member '{expr.member}' invalid for struct '{struct_symbol}'",
                    expr.loc,
                )
                return False
        elif isinstance(expr, (cpt.FunctionCall, cpt.Struct)):
            # For now, this can only be a struct instantiation
            if expr.symbol not in context.structs:
                log.error(
                    f"general functions unsupported\n    {expr}",
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
                    f"struct instantiation/function call does not match signature."
                    f"\n    Found:    {expr.symbol}({', '.join([str(t) for t in actual_types])})"
                    f"\n    Expected: {expr.symbol}({', '.join([str(t) for t in target_types])})",
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
                    f"set aggregation set must be Set type (found '{s.type}')",
                    expr.loc,
                )
                return False

            if expr.operator in {
                cpt.SetAggregationKind.FOR_EXACTLY,
                cpt.SetAggregationKind.FOR_AT_MOST,
                cpt.SetAggregationKind.FOR_AT_LEAST,
            }:
                if not context.enable_booleanizer:
                    log.error(
                        "parameterized set aggregation operators require Booleanizer\n    did you mean to enable the booleanizer?",
                        expr.loc,
                    )
                    return False

                n = cast(cpt.Expression, expr.get_num())
                if not types.is_integer_type(n.type):
                    log.error(
                        f"parameter for set aggregation must be integer type (found '{n.type}')",
                        expr.loc,
                    )
                    return False

            e: cpt.Expression = expr.get_expr()

            if e.type != types.BoolType():
                log.error(
                    f"set aggregation expression must be 'bool' (found '{expr.type}')",
                    expr.loc,
                )
                return False

            expr.type = types.BoolType(expr.type.is_const and s.type.is_const)
        elif isinstance(expr, cpt.TemporalOperator):
            is_const = True

            for child in expr.children:
                is_const = is_const and child.type.is_const
                if child.type != types.BoolType():
                    log.error(
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'bool'\n    {expr}",
                        expr.loc,
                    )
                    return False

            # check for mixed-time formulas
            if cpt.is_future_time_operator(expr):
                if context.is_past_time():
                    log.error(
                        f"mixed-time formulas unsupported, found FT formula in PTSPEC\n    {expr}",
                        expr.loc,
                    )
                    return False
            elif cpt.is_past_time_operator(expr):
                if context.is_future_time():
                    log.error(
                        f"mixed-time formulas unsupported, found PT formula in FTSPEC\n    {expr}",
                        expr.loc,
                    )
                    return False

            interval = expr.interval
            if not interval:
                log.internal(
                    f"interval not set for temporal operator\n    {expr}",
                )
                return False

            if interval.lb > interval.ub:
                log.error(
                    f"time interval invalid, lower bound must less than or equal to upper bound [{interval.lb},{interval.ub}]",
                    expr.loc,
                )
                return False

            expr.type = types.BoolType(is_const)
        elif isinstance(expr, cpt.SymbolicTemporalOperator):
            is_const = True

            for child in expr.children:
                is_const = is_const and child.type.is_const
                if child.type != types.BoolType():
                    log.error(
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'bool'\n    {expr}",
                        expr.loc,
                    )
                    return False

            expr.type = types.BoolType(is_const)
        elif cpt.is_min_max_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const = True

            for child in expr.children:
                is_const = is_const and child.type.is_const
                if child.type != types.IntType():
                    log.error(
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'int'\n    {expr}",
                        expr.loc,
                    )
                    return False

            expr.type = types.IntType(is_const)
        elif cpt.is_bitwise_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const = True

            if not context.enable_booleanizer:
                log.error(
                    f"found Booleanizer expression, but Booleanizer expressions disabled\n    {expr}",
                    expr.loc,
                )
                return False

            new_type = expr.children[0].type

            if all([c.type.is_const for c in expr.children]):
                new_type.is_const = True

            for child in expr.children:
                if isinstance(child, cpt.ArrayExpression) or isinstance(child, cpt.ArraySlice):
                    log.error(
                        f"Bitwise operators not supported on arrays \n\t{expr}",
                        expr.loc,
                    )
                    return False
                elif child.type != new_type or not types.is_integer_type(child.type):
                    log.error(
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected '{new_type}'\n    {expr}",
                        expr.loc,
                    )
                    return False

            expr.type = new_type
        elif cpt.is_arithmetic_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const = True

            if not context.enable_booleanizer:
                log.error(
                    f"found Booleanizer expression, but Booleanizer expressions disabled\n    {expr}",
                    expr.loc,
                )
                return False

            new_type = expr.children[0].type

            if all([c.type.is_const for c in expr.children]):
                new_type.is_const = True

            if expr.operator is cpt.OperatorKind.ARITHMETIC_DIVIDE:
                rhs = expr.children[1]
                # TODO: disallow division by non-const expression entirely
                if isinstance(rhs, cpt.Constant) and rhs.value == 0:
                    log.error(
                        f"divide by zero\n    {expr}",
                        expr.loc,
                    )
                    return False
                
            if expr.operator is cpt.OperatorKind.ARITHMETIC_SQRT:
                rhs = expr.children[0]
                if rhs.type == types.IntType():
                    log.error(
                        f"square root invalid for integer expressions ({rhs}).\n    {expr}",
                        expr.loc,
                    )
                    return False
            
            if expr.operator is cpt.OperatorKind.ARITHMETIC_POWER:
                lhs = expr.children[0]
                rhs = expr.children[1]
                if lhs.type == types.IntType():
                    if isinstance(rhs, cpt.Constant):
                        if rhs.value < 0:
                            log.error(
                                f"power function invalid for integer expressions with negative exponents ({rhs}).\n    {expr}",
                                expr.loc,
                            )
                            return False
                    elif types.IntType.is_signed and not isinstance(rhs, cpt.CurrentTimestamp):
                        log.error(
                            f"power function invalid for integer expressions with possible negative integer exponents ({rhs}).\n    {expr}",
                            expr.loc,
                        )
                        return False

            for child in expr.children:
                if isinstance(child, cpt.ArrayExpression) or isinstance(child, cpt.ArraySlice):
                    log.error(
                        f"Arithmetic operators not supported on arrays \n\t{expr}",
                        expr.loc,
                    )
                    return False
                elif child.type != new_type:
                    log.error(
                        f"operand of '{expr}' must be of homogeneous type\n    "
                        f"Found {child.type} and {new_type}",
                        expr.loc,
                    )
                    return False

            expr.type = new_type
        elif cpt.is_relational_operator(expr):
            expr = cast(cpt.Operator, expr)
            lhs = expr.children[0]
            rhs = expr.children[1]

            if not context.enable_booleanizer and expr.operator not in {
                cpt.OperatorKind.EQUAL,
                cpt.OperatorKind.NOT_EQUAL,
            }:
                log.error(
                    f"found Booleanizer expression, but Booleanizer expressions disabled\n    {expr}",
                    expr.loc,
                )
                return False
            
            if types.is_enum_type(lhs.type) and lhs.type.symbol not in context.enums and rhs.type.symbol in context.enums:
                if lhs.type.symbol not in context.enums[rhs.type.symbol]:
                    log.error(
                    f"Invalid operands for '{expr.symbol}', {lhs.type.symbol} is not a member of {rhs.type.symbol}\n\t{expr}",
                        expr.loc,
                    )
                    return False
                lhs.type = rhs.type
            elif types.is_enum_type(rhs.type) and rhs.type.symbol not in context.enums and lhs.type.symbol in context.enums:
                if rhs.type.symbol not in context.enums[lhs.type.symbol]:
                    log.error(
                    f"Invalid operands for '{expr.symbol}', {rhs.type.symbol} is not a member of {lhs.type.symbol}\n\t{expr}",
                        expr.loc,
                    )
                    return False
                rhs.type = lhs.type
            elif types.is_enum_type(lhs.type) and lhs.type.symbol not in context.enums and \
                types.is_enum_type(rhs.type) and rhs.type.symbol not in context.enums:
                    log.error(
                        f"Invalid operands for '{expr.symbol}', cannot both be enum members\n\t{expr}",
                        expr.loc,
                    )
                    return False

            if lhs.type != rhs.type:
                log.error(
                    f"Invalid operands for '{expr.symbol}', must be of same type (found '{lhs.type}' and '{rhs.type}')\n    {expr}",
                    expr.loc,
                )
                return False

            expr.type = types.BoolType(lhs.type.is_const and rhs.type.is_const)
        elif cpt.is_logical_operator(expr):
            expr = cast(cpt.Operator, expr)
            is_const = True

            for child in expr.children:
                is_const = is_const and child.type.is_const
                if child.type != types.BoolType():
                    log.error(
                        f"Invalid operands for '{expr.symbol}', found '{child.type}' ('{child}') but expected 'bool'\n    {expr}",
                        expr.loc,
                    )
                    return False

            expr.type = types.BoolType(is_const)
        elif cpt.is_prev_operator(expr):
            expr = cast(cpt.Operator, expr)
            
            initial_expr = expr.children[0]
            prev_expr = expr.children[1]
            if types.is_enum_type(initial_expr.type) and initial_expr.type.symbol not in context.enums \
                and prev_expr.type.symbol in context.enums:
                    if initial_expr.type.symbol not in context.enums[prev_expr.type.symbol]:
                        log.error(
                        f"Invalid operands for '{expr.symbol}', {initial_expr.type.symbol} is not a member of {prev_expr.type.symbol}\n\t{expr}",
                            expr.loc,
                        )
                        return False
                    initial_expr.type = prev_expr.type
            elif initial_expr.type.symbol in context.enums:
                log.error(
                    f"Invalid initial value for '{expr.symbol}', must be of constant type (found '{initial_expr}')\n\t{expr}",
                    expr.loc,
                )
                return False
            elif types.is_enum_type(initial_expr.type) and initial_expr.type.symbol not in context.enums \
                and types.is_enum_type(prev_expr.type) and prev_expr.type.symbol not in context.enums:
                    log.error(
                        f"Invalid operands for '{expr.symbol}', cannot both be enum members\n\t{expr}",
                        expr.loc,
                    )
                    return False
            elif initial_expr.type != prev_expr.type:
                log.error(
                    f"Invalid operands for '{expr.symbol}', must be of same type (found '{initial_expr.type}' and '{prev_expr.type}')\n\t{expr}",
                    expr.loc,
                )
                return False
            
            if initial_expr.symbol in context.definitions: # Check if definition is constant
                initial_expr = context.definitions[initial_expr.symbol]
            
            if not isinstance(initial_expr, cpt.Constant) and not types.is_enum_type(initial_expr.type):
                log.error(
                    f"Invalid initial value for '{expr.symbol}', must be of constant type (found '{initial_expr}')\n\t{expr}",
                    expr.loc,
                )
                return False
            for child in expr.get_descendants():
                if cpt.is_prev_operator(child):
                    log.error(
                        f"Invalid nested previous statements, ({child}).\n\t{expr}",
                        expr.loc,
                    )
                    return False
            expr.type = initial_expr.type

        else:
            log.error(
                f"invalid expression of type '{type(expr)}'\n    {expr}",
                expr.loc,
            )
            return False

    return True


def type_check_section(section: cpt.ProgramSection, symbols: set[str], context: cpt.Context, options: dict[str, Any]) -> bool:
    status = True

    if isinstance(section, cpt.InputSection):
        for declaration in section.signal_decls:
            for signal in declaration.variables:
                if signal in symbols:
                    status = False
                    log.error(
                        f"symbol '{signal}' already in use",
                        declaration.loc,
                    )

                if declaration.type.symbol in context.enums:
                    declaration.type = types.EnumType(declaration.type.symbol)

                symbols.add(signal)
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
                [type_check_expr(sig, context, options) for sig in signals]
    elif isinstance(section, cpt.DefineSection):
        for definition in section.defines:
            if definition.symbol in symbols:
                status = False
                log.error(
                    f"symbol '{definition.symbol}' already in use",
                    definition.loc, 
                )

            symbols.add(definition.symbol)
            is_good_def = type_check_expr(definition.expr, context, options)
            if is_good_def:
                context.add_definition(definition.symbol, definition.expr)
            status = status and is_good_def
    elif isinstance(section, cpt.StructSection):
        for struct in section.struct_defs:
            if struct.symbol in symbols:
                status = False
                log.error(
                    f"symbol '{struct.symbol}' already in use",
                    struct.loc,
                )

            symbols.add(struct.symbol)
            context.add_struct(struct.symbol, struct.members)
    elif isinstance(section, cpt.EnumSection):
        for enum in section.enum_defs:
            if enum.symbol in context.get_symbols():
                status = False
                log.error(
                    f"Symbol '{enum.symbol}' already in use",
                    enum.loc,
                )
            for member_name, member_expr in enum.members.items():
                if (not isinstance(member_expr, cpt.Constant)) or (not types.is_integer_type(member_expr.type)):
                    status = False
                    log.error(
                        f"Enum member {member_name} must be a constant integer, found {member_expr.type}",
                        enum.loc,
                    )
                if member_name in context.get_symbols() or member_name == enum.symbol:
                    status = False
                    log.error(
                        f"Symbol '{member_name}' already in use",
                        enum.loc,
                    )
            context.add_enum(enum.symbol, enum.members)
    elif isinstance(section, cpt.SpecSection):
        if isinstance(section, cpt.FutureTimeSpecSection):
            context.set_future_time()
        else:
            context.set_past_time()

        for spec in section.specs:
            if spec.symbol != "" and spec.symbol in symbols:
                status = False
                log.error(
                    f"symbol '{spec.symbol}' already in use",
                    spec.loc,
                )

            symbols.add(spec.symbol)
            is_good_spec = type_check_expr(spec, context, options)
            status = status and is_good_spec

    return status

def type_check(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Type check a program and return a context object that contains the type information for the program.

    `options` is a dictionary of options that must contain the following keys (should be defined as global options in the main module):
    - `spec_filename`: The path to the specification file
    - `enable_booleanizer`: Whether to enable the booleanizer

    Returns:
        None if type checking fails, the context object otherwise.
    """
    status = True
    for section in program.sections:
        is_good = type_check_section(section, set(), context, options)
        status = status and is_good

    log.debug(1, f"type checking result: {status}")
    program.is_well_typed = status
    return command.ReturnCode.SUCCESS if status else command.ReturnCode.ERROR

type_check_command = command.Command(
    name="type_check",
    description="Type check the program and construct a context.",
    options=[],
    func=type_check,
    guards=[command.VALID_PROGRAM],
)
command.CommandRegistry.register(type_check_command)
