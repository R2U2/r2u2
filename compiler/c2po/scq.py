from __future__ import annotations
from typing import cast, Any
from c2po import cpt, log, types, command

def compute_scq_sizes(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Computes SCQ sizes for each node. Returns the total SCQ size.
    
    `options` is a dictionary of options for the SCQ size computation.
    - `scq-constant`: A constant to add to the SCQ size of each node
    """
    scq_constant = options["scq_constant"]
    total_scq_size = 0

    for expr in cpt.postorder(cast("list[cpt.Expression]", program.get_specs()), context):
        if isinstance(expr, cpt.SpecSection):
            continue

        if isinstance(expr, cpt.Formula):
            expr.scq_size = 1 + scq_constant
            total_scq_size += expr.scq_size
            expr.scq = (
                total_scq_size - expr.scq_size,
                total_scq_size,
            )
            continue

        if (
            expr.engine != types.R2U2Engine.TEMPORAL_LOGIC
            and expr not in context.atomic_id_map
        ):
            continue

        # Constant booleans have no SCQ size
        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type):
            expr.scq_size = 0
            expr.scq = (
                total_scq_size,
                total_scq_size,
            )
            continue

        max_wpd = max([sibling.wpd for sibling in expr.get_siblings()] + [0])
        expr.scq_size = max(max_wpd - expr.bpd, 0) + 1 + scq_constant
        total_scq_size += expr.scq_size
        expr.scq = (
            total_scq_size - expr.scq_size,
            total_scq_size,
        )

        log.debug(2, f"siblings of {repr(expr)} = {[repr(sibling) for sibling in expr.get_siblings()]}")
        log.debug(2, f"max_wpd: {max_wpd}, expr.bpd: {expr.bpd}")

    for expr in program.postorder(context):
        if (
            expr.engine != types.R2U2Engine.TEMPORAL_LOGIC
            and expr not in context.atomic_id_map
        ):
            continue
        log.debug(2, f"scq_size({repr(expr)}) = {expr.scq_size}")
    log.debug(2, f"program SCQ size: {total_scq_size}")

    program.total_scq_size = total_scq_size
    context.stats.total_scq_size = total_scq_size

    return command.ReturnCode.SUCCESS

compute_scq_sizes_command = command.Command(
    name="compute_scq_sizes",
    description="Compute SCQ sizes for the program. Likely does not need to be run manually.",
    options=[{
        "name": "scq-constant",
        "description": "A constant to add to the SCQ size of each node",
        "required": False,
        "type": int,
        "default": 0,
        "choices": None
    }],
    func=compute_scq_sizes,
    # FIXME: SCQ computation gets invalidated any time the program is modified, we need to check for this
    guards=[command.VALID_PROGRAM, command.WELL_TYPED, command.DESUGARED],
)
command.CommandRegistry.register(compute_scq_sizes_command)
