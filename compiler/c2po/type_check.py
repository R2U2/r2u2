from .ast import *

def type_check_expr(expr: C2POExpression, context: C2POContext) -> bool:
    status = True

    if isinstance(expr, C2POSpecification):
        status = status and type_check_expr(expr.get_expr(), context)
    elif isinstance(expr, C2POConstant):
        pass
    elif isinstance(expr, C2POSignal):
        if context.assembly_enabled and expr.symbol not in context.signal_mapping:
            status = False
            logger.error(f"{expr.ln} Mapping does not contain signal '{expr.symbol}'.")

        if expr.symbol in context.signal_mapping:
            expr.signal_id = context.signal_mapping[expr.symbol]

        expr.type = context.signals[expr.symbol]
    elif isinstance(expr, C2POAtomicChecker):
        if expr.symbol not in context.atomic_checkers:
            status = False
            logger.error(f"{expr.ln}: Atomic checker '{expr.symbol}' not defined.")
    elif isinstance(expr, C2POVariable):
        symbol = expr.symbol
        if symbol in context.variables:
            expr.type = context.variables[symbol]
        elif symbol in context.definitions:
            expr.type = context.definitions[symbol].type
        elif symbol in context.structs:
            logger.error(f"{expr.ln}: Defined structs may not be used as variables. Maybe you mean to declare the struct first?")
            status = False
        elif symbol in context.atomic_checkers:
            expr.type = C2POBoolType(False)
        elif symbol in context.specifications:
            expr.type = C2POBoolType(False)
        elif symbol in context.contracts:
            logger.error(f"{expr.ln}: Contracts not allowed as subexpressions ('{symbol}').")
            status = False
        else:
            logger.error(f"{expr.ln}: Symbol '{symbol}' not recognized.")
            status = False
    elif isinstance(expr, C2POFunctionCall):
        # For now, this can only be a struct instantiation
        if expr.symbol not in context.structs and expr.symbol not in context.atomic_checker_filters:
            logger.error(f"{expr.ln}: Functions unsupported.\n\t{expr}")
            status =  False

        for arg in expr.get_children():
            status = status and type_check_expr(arg, context)

        if expr.symbol in context.structs:
            expr.type = C2POStructType(False, expr.symbol)
    elif isinstance(expr, C2PORelationalOperator): 
        lhs: C2POExpression = expr.get_lhs()
        rhs: C2POExpression = expr.get_rhs()
        status = status and type_check_expr(lhs, context)
        status = status and type_check_expr(rhs, context)

        if lhs.type != rhs.type:
            status = False
            logger.error(f"{expr.ln}: Invalid operands for '{expr.symbol}', must be of same type (found '{lhs.type}' and '{rhs.type}')\n\t{expr}")

        expr.type = C2POBoolType(lhs.type.is_const and rhs.type.is_const)
    elif isinstance(expr, C2POArithmeticOperator):
        is_const: bool = True

        if context.implementation != R2U2Implementation.C:
            status = False
            logger.error(f"{expr.ln}: Arithmetic operators only support in C version of R2U2.\n\t{expr}")

        if not context.booleanizer_enabled:
            status = False
            logger.error(f"{expr.ln}: Found Booleanizer expression, but Booleanizer expressions disabled\n\t{expr}")

        for c in expr.get_children():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const

        t: C2POType = expr.get_child(0).type
        t.is_const = is_const

        if isinstance(expr, C2POArithmeticDivide):
            rhs: C2POExpression = expr.get_rhs()
            if isinstance(rhs, C2POConstant) and rhs.get_value() == 0:
                status = False
                logger.error(f"{expr.ln}: Divide by zero\n\t{expr}")

        for c in expr.get_children():
            if c.type != t:
                status = False
                logger.error(f"{expr.ln}: Operand of '{expr}' must be of homogeneous type (found '{c.type}' and '{t}')")

        expr.type = t
    elif isinstance(expr, C2POBitwiseOperator):
        is_const: bool = True

        if context.implementation != R2U2Implementation.C:
            status = False
            logger.error(f"{expr.ln}: Bitwise operators only support in C version of R2U2.\n\t{expr}")

        if not context.booleanizer_enabled:
            status = False
            logger.error(f"{expr.ln}: Found context.booleanizer_enabled expression, but Booleanizer expressions disabled\n\t{expr}")

        t: C2POType = C2PONoType()
        for c in expr.get_children():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const
            t = c.type

        t.is_const = is_const

        for c in expr.get_children():
            if c.type != t or not is_integer_type(c.type):
                status = False
                logger.error(f"{expr.ln}: Invalid operands for '{expr.symbol}', found '{c.type}' ('{c}') but expected '{expr.get_child(0).type}'\n\t{expr}")

        expr.type = t
    elif isinstance(expr, C2POLogicalOperator):
        is_const: bool = True

        for c in expr.get_children():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const
            if c.type != C2POBoolType(False):
                status = False
                logger.error(f"{expr.ln}: Invalid operands for '{expr.symbol}', found '{c.type}' ('{c}') but expected 'bool'\n\t{expr}")

        expr.type = C2POBoolType(is_const)
    elif isinstance(expr, C2POTemporalOperator):
        is_const: bool = True

        for c in expr.get_children():
            status = status and type_check_expr(c, context)
            is_const = is_const and c.type.is_const
            if c.type != C2POBoolType(False):
                status = False
                logger.error(f"{expr.ln}: Invalid operands for '{expr.symbol}', found '{c.type}' ('{c}') but expected 'bool'\n\t{expr}")

        # check for mixed-time formulas
        if isinstance(expr, C2POFutureTimeOperator):
            if context.is_past_time():
                status = False
                logger.error(f"{expr.ln}: Mixed-time formulas unsupported, found FT formula in PTSPEC.\n\t{expr}")
        elif isinstance(expr, C2POPastTimeOperator):
            if context.implementation != R2U2Implementation.C:
                status = False
                logger.error(f"{expr.ln}: Past-time operators only support in C version of R2U2.\n\t{expr}")
            if context.is_future_time():
                status = False
                logger.error(f"{expr.ln}: Mixed-time formulas unsupported, found PT formula in FTSPEC.\n\t{expr}")

        if expr.interval.lb > expr.interval.ub:
            status = False
            logger.error(f"{expr.ln}: Time interval invalid, lower bound must less than or equal to upper bound.\n\t[{expr.interval.lb},{expr.interval.ub}]")

        expr.type = C2POBoolType(is_const)
    elif isinstance(expr, C2POSet):
        t: C2POType = C2PONoType()
        is_const: bool = True

        for m in expr.get_children():
            status = status and type_check_expr(m, context)
            is_const = is_const and m.type.is_const
            t = m.type

        for m in expr.get_children():
            if m.type != t:
                status = False
                logger.error(f"{expr.ln}: Set '{expr}' must be of homogeneous type (found '{m.type}' and '{t}')")

        expr.type = C2POSetType(is_const, t)
    elif isinstance(expr, C2POSetAggOperator):
        s: C2POSet = expr.get_set()
        boundvar: C2POVariable = expr.get_boundvar()

        status = status and type_check_expr(s, context)

        if isinstance(s.type, C2POSetType):
            context.add_variable(boundvar.symbol, s.type.member_type)
        else:
            status = False
            logger.error(f"{expr.ln}: Set aggregation set must be Set type (found '{s.type}')")

        if isinstance(expr, C2POForExactly) or isinstance(expr, C2POForAtLeast) or isinstance(expr, C2POForAtMost):
            if not context.booleanizer_enabled:
                status = False
                logger.error(f"{expr.ln}: Parameterized set aggregation operators require Booleanizer, but Booleanizer not enabled.")

            n: C2POExpression = expr.get_num()
            status = status and type_check_expr(n, context)
            if not is_integer_type(n.type):
                status = False
                logger.error(f"{expr.ln}: Parameter for set aggregation must be integer type (found '{n.type}')")

        e: C2POExpression = expr.get_expr()
        status = status and type_check_expr(e, context)

        if e.type != C2POBoolType(False):
            status = False
            logger.error(f"{expr.ln}: Set aggregation expression must be 'bool' (found '{expr.type}')")

        expr.type = C2POBoolType(expr.type.is_const and s.type.is_const)
    elif isinstance(expr, C2POStruct):
        is_const: bool = True

        for member in expr.get_children():
            status = status and type_check_expr(member, context)
            is_const = is_const and member.type.is_const

        for (m,t) in context.structs[expr.symbol].items():
            if expr.get_member(m).type != t:
                logger.error(f"{expr.ln}: Member '{m}' invalid type for struct '{expr.symbol}' (expected '{t}' but got '{expr.get_member(m).type}')")

        expr.type = C2POStructType(is_const, expr.symbol)
    elif isinstance(expr, C2POStructAccess):
        struct = expr.get_struct()
        status = status and type_check_expr(struct, context)

        struct_symbol = expr.get_struct().type.name
        if struct_symbol not in context.structs:
            logger.error(f"{expr.ln}: Struct '{struct_symbol}' not defined ({expr}).")
            status = False
        
        valid_member: bool = False
        for (m,t) in context.structs[struct_symbol].items():
            if expr.member == m:
                expr.type = t
                valid_member = True

        if not valid_member:
            status = False
            logger.error(f"{expr.ln}: Member '{expr.member}' invalid for struct '{struct_symbol}'")
    else:
        logger.error(f"{expr.ln}: Invalid expression ({type(expr)})\n\t{expr}")
        status = False

    return status


def type_check_atomic(atomic: C2POAtomicCheckerDefinition, context: C2POContext) -> bool:
    status = True

    relational_expr = atomic.get_expr()

    if not isinstance(relational_expr, C2PORelationalOperator):
        logger.error(f"{atomic.ln}: Atomic checker definition not a relation.\n\t{atomic}")
        return False

    lhs = relational_expr.get_lhs()
    rhs = relational_expr.get_rhs()

    if isinstance(lhs, C2POFunctionCall):
        if lhs.symbol not in context.atomic_checker_filters:
            logger.error(f"{lhs.ln}: Invalid atomic checker filter ('{lhs.symbol}')")
            status = False

        if lhs.num_children() != len(context.atomic_checker_filters[lhs.symbol]):
            logger.error(f"{lhs.ln}: Atomic checker filter argument mismatch. Expected {len(context.atomic_checker_filters[lhs.symbol])} arguments, got {lhs.num_children()}")
            status = False
        
        for arg, target_type in zip(lhs.get_children(), context.atomic_checker_filters[lhs.symbol]):
            if not isinstance(arg, C2POLiteral):
                logger.error(f"{arg.ln}: Atomic checker filter argument '{arg}' is not a signal nor constant.")
                status = False

            type_check_expr(arg, context) # assigns signals their types
            
            if arg.type != target_type:
                logger.error(f"{arg.ln}: Atomic checker filter argument '{arg}' does not match expected type. Expected {target_type}, found {arg.type}.")
                status = False
    elif isinstance(lhs, C2POSignal):
        type_check_expr(lhs, context)
    else:
        logger.error(f"{lhs.ln}: Left-hand side of atomic checker definition not a filter nor  signal.\n\t{lhs}")
        status = False

    if not isinstance(rhs, C2POLiteral):
        logger.error(f"{rhs.ln}: Right-hand side of atomic checker definition not a constant or signal.\n\t{rhs}")
        status = False

    return status


def type_check_section(section: C2POSection, context: C2POContext) -> bool:
    status = True

    if isinstance(section, C2POInputSection):
        for declaration in section.get_signals():
            for signal in declaration.get_symbols():
                if signal in context.get_symbols():
                    status = False
                    logger.error(f"{declaration.ln}: Symbol '{signal}' already in use.")

                context.add_signal(signal, declaration.get_type())
    elif isinstance(section, C2PODefineSection):
        for definition in section.get_definitions():
            if definition.symbol in context.get_symbols():
                status = False
                logger.error(f"{definition.ln}: Symbol '{definition.symbol}' already in use.")

            status = status and type_check_expr(definition.get_expr(), context)
            if status:
                context.add_definition(definition.symbol, definition.get_expr())
    elif isinstance(section, C2POStructSection):
        for struct in section.get_structs():
            if struct.symbol in context.get_symbols():
                status = False
                logger.error(f"{struct.ln}: Symbol '{struct.symbol}' already in use.")

            context.add_struct(struct.symbol, struct.get_members())
    elif isinstance(section, C2POAtomicSection):
        for atomic in section.get_atomic_checkers():
            if atomic.symbol in context.get_symbols():
                status = False
                logger.error(f"{atomic.ln}: Symbol '{atomic.symbol}' already in use.")

            status = status and type_check_atomic(atomic, context)
            if status:
                context.add_atomic(atomic.symbol, atomic.get_expr())
    elif isinstance(section, C2POSpecSection):
        if isinstance(section, C2POFutureTimeSpecSection):
            if context.has_future_time:
                logger.error(f"Only one FTSPEC section allowed.")
                status = False
            context.has_future_time = True
            context.set_future_time()
        else:
            if context.has_past_time:
                logger.error(f"Only one PTSPEC section allowed.")
                status = False
            context.has_past_time = True
            context.set_past_time()

        for spec in section.get_specs():
            if spec.symbol != "" and spec.symbol in context.get_symbols():
                status = False
                logger.error(f"{spec.ln}: Symbol '{spec.symbol}' already in use.")

            if isinstance(spec, C2POSpecification):
                status = status and type_check_expr(spec, context)
                if status:
                    context.add_specification(spec.symbol, spec)
            elif isinstance(spec, C2POContract):
                status = status and type_check_expr(spec.get_assumption(), context)
                status = status and type_check_expr(spec.get_guarantee(), context)
                if status:
                    context.add_contract(spec.symbol, spec)
        
    return status


def type_check(
    program: C2POProgram, 
    impl: R2U2Implementation, 
    mission_time: int,
    atomic_checkers: bool,
    booleanizer: bool,
    assembly_enabled: bool,
    signal_mapping: SignalMapping
) -> Tuple[bool, C2POContext]:
    status: bool = True
    context = C2POContext(impl, mission_time, atomic_checkers, booleanizer, assembly_enabled, signal_mapping)
    
    for section in program.get_sections():
        status = status and type_check_section(section, context)

    return (status, context)




# def type_check_atomic(name: str, node: C2PONode) -> ATInstruction|None:
#     nonlocal status

#     if isinstance(node, C2PORelationalOperator):
#         lhs: C2PONode = node.get_lhs()
#         rhs: C2PONode = node.get_rhs()

#         filter: str = ""
#         filter_args: List[C2PONode] = []

#         # type check left-hand side
#         if isinstance(lhs, C2POFunction):
#             if not lhs.name in AT_FILTER_TABLE:
#                 status = False
#                 logger.error(f"{node.ln}: Atomic "{name}" malformed, filter "{lhs.name}" undefined.\n\t{node}")
#                 return

#             if not len(AT_FILTER_TABLE[lhs.name][0]) == len(lhs.get_children()):
#                 status = False
#                 logger.error(f"{node.ln}: Atomic "{name}" malformed, filter "{lhs.name}" has incorrect number of arguments (expected {len(AT_FILTER_TABLE[lhs.name][0])}, found {len(lhs.get_children())}).\n\t{node}")
#                 return

#             for i in range(0, len(lhs.get_children())):
#                 arg: C2PONode = lhs.get_child(i)

#                 if isinstance(arg, C2POVariable):
#                     if arg.name not in program.signals:
#                         status = False
#                         logger.error(f"{node.ln}: Atomic "{name}" malformed, {arg.name} not a valid signal.\n\t{node}")
#                         return

#                     sig = C2POSignal(arg.ln, arg.name, program.signals[arg.name])
#                     if arg.name not in program.signal_mapping:
#                         status = False
#                         logger.error(f"{arg.ln}: Signal '{arg.name}' not referenced in signal mapping.")

#                     sig.sid = program.signal_mapping[arg.name]
#                     arg.replace(sig)

#                     if sig.type != AT_FILTER_TABLE[lhs.name][0][i]:
#                         status = False
#                         logger.error(f"{node.ln}: Atomic "{name}" malformed, left- and right-hand sides must be of same type (found "{sig.type}" and "{AT_FILTER_TABLE[lhs.name][0][i]}").\n\t{node}")
#                         return
#                 elif isinstance(arg, C2POConstant):
#                     if arg.type != AT_FILTER_TABLE[lhs.name][0][i]:
#                         status = False
#                         logger.error(f"{node.ln}: Atomic "{name}" malformed, left- and right-hand sides must be of same type (found "{arg.type}" and "{AT_FILTER_TABLE[lhs.name][0][i]}").\n\t{node}")
#                         return
#                 else:
#                     status = False
#                     logger.error(f"{node.ln}: Filter arguments must be signals or constants (found "{type(arg)}").\n\t{node}")

#             filter = lhs.name
#             filter_args = lhs.get_children()
#             lhs.type = AT_FILTER_TABLE[lhs.name][1]
#         elif isinstance(lhs, C2POVariable):
#             if lhs.name in program.signals:
#                 sig = C2POSignal(lhs.ln, lhs.name, program.signals[lhs.name])
#                 if lhs.name in program.signal_mapping:
#                     sig.sid = program.signal_mapping[lhs.name]
#                     lhs.replace(sig)
#                     lhs.type = sig.type
#                 else:
#                     status = False
#                     logger.error(f"{lhs.ln}: Signal '{lhs.name}' not referenced in signal mapping.")

#                 filter = sig.type.name
#                 filter_args = [sig]
#             elif lhs.name in program.definitions and isinstance(program.definitions[lhs.name], C2POSpecification):
#                 lhs.replace(program.definitions[lhs.name])
#                 filter = "formula"
#                 filter_args = [program.definitions[lhs.name]]
#                 lhs.type = C2POBoolType(False)
#         else:
#             status = False
#             logger.error(f"{node.ln}: Atomic "{name}" malformed, expected filter or signal for left-hand side.\n\t{node}")
#             return

#         # type check right-hand side
#         if isinstance(rhs, C2POVariable):
#             if not rhs.name in program.signals:
#                 status = False
#                 logger.error(f"{rhs.ln}: Signal '{rhs.name}' not declared.")

#             if not rhs.name in program.signal_mapping:
#                 status = False
#                 logger.error(f"{rhs.ln}: Signal '{rhs.name}' not referenced in signal mapping.")

#             if program.signals[rhs.name] != lhs.type:
#                 status = False
#                 logger.error(f"{node.ln}: 1 Atomic "{name}" malformed, left- and right-hand sides must be of same type (found "{lhs.type}" and "{rhs.type}").\n\t{node}")
#                 return

#             sig = C2POSignal(rhs.ln, rhs.name, program.signals[rhs.name])
#             sig.sid = program.signal_mapping[sig.name]
#             rhs.replace(sig)
#             rhs = sig
#         elif isinstance(rhs, C2POConstant):
#             if lhs.type != rhs.type:
#                 status = False
#                 logger.error(f"{node.ln}: Atomic "{name}" malformed, left- and right-hand sides must be of same type (found "{lhs.type}" and "{rhs.type}").\n\t{node}")
#                 return
#         else:
#             status = False
#             logger.error(f"{node.ln}: Atomic "{name}" malformed, expected signal or constant for right-hand side.\n\t{node}")
#             return

#         return ATInstruction(node.ln, name, filter, filter_args, node, rhs)
#     elif not isinstance(node, ATInstruction):
#         status = False
#         logger.error(f"{node.ln}: Atomic "{name}" malformed, expected relational operator at top-level.\n\t{node}")
#         return