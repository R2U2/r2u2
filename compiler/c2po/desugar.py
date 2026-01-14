from typing import Any, cast
from c2po import cpt, log, command, types

def expand_definitions(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Expands each definition symbol in the definitions and specifications of `program` to its expanded definition. This is essentially macro expansion.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for expr in [
        expr
        for define in context.definitions.values()
        for expr in cpt.postorder(define, context)
    ] + [expr for expr in program.postorder(context)]:
        if not isinstance(expr, cpt.Variable):
            continue

        if expr.symbol in context.definitions:
            expr.replace(context.definitions[expr.symbol])
        elif expr.symbol in context.specifications:
            expr.replace(context.specifications[expr.symbol].get_expr())

    log.debug(1, f"post definition expansion:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

expand_definitions_command = command.Command(
    name="expand_definitions",
    description="Expands each definition symbol in the definitions and specifications of `program` to its expanded definition. This is essentially macro expansion.",
    options=[],
    func=expand_definitions,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(expand_definitions_command)

def convert_function_calls_to_structs(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Converts each function call in `program` that corresponds to a struct instantiation to a `cpt.Struct`.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for expr in [
        expr
        for define in context.definitions.values()
        for expr in cpt.postorder(define, context)
    ] + [expr for expr in program.postorder(context)]:
        if not isinstance(expr, cpt.FunctionCall):
            continue

        if expr.symbol not in context.structs:
            continue

        struct_members = [m for m in context.structs[expr.symbol].keys()]
        expr.replace(
            cpt.Struct(
                expr.loc,
                expr.symbol,
                {
                    name: struct_members.index(name)
                    for name in context.structs[expr.symbol].keys()
                },
                expr.children,
            )
        )

    return command.ReturnCode.SUCCESS

convert_function_calls_to_structs_command = command.Command(
    name="convert_function_calls_to_structs",
    description="Converts each function call in `program` that corresponds to a struct instantiation to a `cpt.Struct`.",
    options=[],
    func=convert_function_calls_to_structs,
    guards=[command.WELL_TYPED], 
)
command.CommandRegistry.register(convert_function_calls_to_structs_command)

def resolve_contracts(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Removes each contract from each specification in Program and adds the corresponding conditions to track.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for contract in [
        spec for spec in program.get_specs() if isinstance(spec, cpt.Contract)
    ]:
        new_formulas = [
            cpt.Formula(
                contract.loc,
                f"__{contract.symbol}_active__",
                contract.formula_numbers[0],
                contract.get_assumption(),
            ),
            cpt.Formula(
                contract.loc,
                f"__{contract.symbol}_valid__",
                contract.formula_numbers[1],
                cpt.Operator.LogicalImplies(
                    contract.loc, contract.get_assumption(), contract.get_guarantee()
                ),
            ),
            cpt.Formula(
                contract.loc,
                f"__{contract.symbol}_verified__",
                contract.formula_numbers[2],
                cpt.Operator.LogicalAnd(
                    contract.loc, [contract.get_assumption(), contract.get_guarantee()]
                ),
            ),
        ]

        for formula in new_formulas:
            formula.get_expr().type = types.BoolType()

        new_formulas = cast("list[cpt.Specification]", new_formulas)

        program.replace_spec(contract, new_formulas)

        log.debug(1, f"replaced contract '{contract.symbol}'")

    log.debug(1, f"post contract replacement:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

resolve_contracts_command = command.Command(
    name="resolve_contracts",
    description="Removes each contract from each specification in Program and adds the corresponding conditions to track.",
    options=[],
    func=resolve_contracts,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(resolve_contracts_command)


def unroll_set_aggregation(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Unrolls set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    def resolve_struct_accesses(expr: cpt.Expression, context: cpt.Context) -> None:
        if not isinstance(expr, cpt.StructAccess):
            return

        s = expr.get_struct()
        if not isinstance(s, cpt.Struct):
            return

        member = s.get_member(expr.member)
        if not member:
            raise ValueError(f"Member {expr.member} not found in struct {s} --- issue with type checking\n"
                             f"Please open an issue at {log.ISSUE_URL}.")

        new_type = member.type
        if member:
            expr.replace(member)
            member.type = new_type

    for expr in program.preorder(context):
        if not isinstance(expr, cpt.SetAggregation):
            continue

        if expr.operator is cpt.SetAggregationKind.FOR_EACH:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.LogicalAnd(
                expr.loc,
                [
                    cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                    for e in expr.get_set().children
                ],
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationKind.FOR_SOME:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.LogicalOr(
                expr.loc,
                [
                    cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                    for e in expr.get_set().children
                ],
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationKind.FOR_EXACTLY:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.Equal(
                expr.loc,
                cpt.Operator.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                    types.IntType(),
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationKind.FOR_AT_LEAST:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.GreaterThanOrEqual(
                expr.loc,
                cpt.Operator.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                    types.IntType(),
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)
        elif expr.operator is cpt.SetAggregationKind.FOR_AT_MOST:
            for subexpr in cpt.postorder(expr.get_set(), context):
                resolve_struct_accesses(subexpr, context)

            new = cpt.Operator.LessThanOrEqual(
                expr.loc,
                cpt.Operator.ArithmeticAdd(
                    expr.loc,
                    [
                        cpt.rename(expr.bound_var, e, expr.get_expr(), context)
                        for e in expr.get_set().children
                    ],
                    types.IntType(),
                ),
                expr.get_num(),
            )

            expr.replace(new)

            for subexpr in cpt.postorder(new, context):
                resolve_struct_accesses(subexpr, context)

    log.debug(1, f"post set aggregation unrolling:\n{repr(program)}")

    return command.ReturnCode.SUCCESS

unroll_set_aggregation_command = command.Command(
    name="unroll_set_aggregation",
    description="Unrolls set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction.",
    options=[],
    func=unroll_set_aggregation,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(unroll_set_aggregation_command)


def resolve_struct_accesses(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Resolves struct access operations to the underlying member expression.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for expr in program.postorder(context):
        if not isinstance(expr, cpt.StructAccess):
            continue

        s = expr.get_struct()
        if not isinstance(s, cpt.Struct):
            continue

        member = s.get_member(expr.member)
        if not member:
            raise ValueError(f"Member {expr.member} not found in struct {s} --- issue with type checking\n"
                             f"Please open an issue at {log.ISSUE_URL}.")

        new_type = member.type
        if member:
            expr.replace(member)
            member.type = new_type

    log.debug(1, f"post struct access resolution:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

resolve_struct_accesses_command = command.Command(
    name="resolve_struct_accesses",
    description="Resolves struct access operations to the underlying member expression.",
    options=[],
    func=resolve_struct_accesses,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(resolve_struct_accesses_command)


def resolve_array_accesses(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Resolves array access operations to the underlying member expression.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for expr in program.postorder(context):
        if not isinstance(expr, cpt.ArrayIndex):
            continue

        # Not all out-of-bounds errors are checked during type checking
        # Ex: a struct has an array member type of uninterpreted size,
        # must check this case here
        if not isinstance(expr.get_array().type, types.ArrayType):
            log.error(f"array access on a non-array expression, did you run type_check first? ({expr})", expr.loc)
            return command.ReturnCode.ERROR
            
        array_type = cast(types.ArrayType, expr.get_array().type)
        if expr.get_index() >= array_type.size:
            log.error(f"out-of-bounds array index ({expr})", expr.loc)
            return command.ReturnCode.ERROR

        array = expr.get_array()
        expr.replace(array.children[expr.get_index()])

    log.debug(1, f"post array access resolution:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

resolve_array_accesses_command = command.Command(
    name="resolve_array_accesses",
    description="Resolves array access operations to the underlying member expression.",
    options=[],
    func=resolve_array_accesses,
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(resolve_array_accesses_command)

desugar_command = command.CompositeCommand(
    name="desugar",
    description="A list of commands to desugar a program. Only C2PO programs need to be desugared.",
    commands=[
        expand_definitions_command,
        convert_function_calls_to_structs_command,
        resolve_contracts_command,
        resolve_struct_accesses_command,
        unroll_set_aggregation_command,
        resolve_struct_accesses_command,
        resolve_array_accesses_command, 
        resolve_struct_accesses_command,
    ],
    guards=[command.WELL_TYPED],
)
command.CommandRegistry.register(desugar_command)
