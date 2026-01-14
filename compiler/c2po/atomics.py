from typing import Any
from c2po import cpt, log, command, types

def compute_atomics(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Compute atomics and store them in `context`. 
    An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine.
    Syntactically equivalent expressions share the same atomic ID.

    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    atomic_id_map: dict[str, int] = {}
    aid: int = 0

    for expr in program.postorder(context):
        if (
            expr.engine == types.R2U2Engine.TEMPORAL_LOGIC 
            or isinstance(expr, cpt.Constant) 
            or expr in context.atomic_id_map
        ):
            continue

        if cpt.to_prefix_str(expr) in atomic_id_map:
            atomic_id = atomic_id_map[cpt.to_prefix_str(expr)]
            context.atomic_id_map[expr] = atomic_id
            context.atomic_expr_map[atomic_id] = expr
            continue

        # we just cast signals as atomics when we have no frontend
        if not context.enable_booleanizer:
            if isinstance(expr, cpt.Signal):
                if expr.signal_id < 0:
                    context.atomic_id_map[expr] = aid
                    atomic_id_map[cpt.to_prefix_str(expr)] = aid
                    context.atomic_expr_map[aid] = expr
                    aid += 1
                    continue

                context.atomic_id_map[expr] = expr.signal_id
                context.atomic_expr_map[expr.signal_id] = expr
                atomic_id_map[cpt.to_prefix_str(expr)] = expr.signal_id
                continue
        elif not isinstance(expr, cpt.Atomic):
            # add atomic node between any TL and BZ nodes
            tl_parents = [
                p for p in expr.parents if p.engine == types.R2U2Engine.TEMPORAL_LOGIC
            ]

            if expr.engine == types.R2U2Engine.BOOLEANIZER and len(tl_parents) > 0:
                log.debug(2, f"adding atomic node between {repr(expr)} and {repr(tl_parents)}")
                new = cpt.Atomic(expr.loc, expr)
                for parent in tl_parents:
                    for i in range(0, len(parent.children)):
                        if id(parent.children[i]) == id(expr):
                            parent.children[i] = new
                    new.parents.add(parent)
                    expr.parents.remove(parent)

                if cpt.to_prefix_str(new) in atomic_id_map:
                    context.atomic_id_map[new] = atomic_id_map[cpt.to_prefix_str(new)]
                    context.atomic_expr_map[atomic_id_map[cpt.to_prefix_str(new)]] = new
                else:
                    context.atomic_id_map[new] = aid
                    atomic_id_map[cpt.to_prefix_str(new)] = aid
                    context.atomic_expr_map[aid] = new
                    aid += 1

    log.debug(
        1, f"computed atomics: [{', '.join(f'({a},{i})' for a,i in context.atomic_id_map.items())}]",
    )

    return command.ReturnCode.SUCCESS

compute_atomics_command = command.Command(
    name="compute_atomics",
    description="Compute atomics and store them in the context. Likely does not need to be run manually. An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine. Syntactically equivalent expressions share the same atomic ID.",
    options=[],
    func=compute_atomics,
    guards=[command.DESUGARED],
)
command.CommandRegistry.register(compute_atomics_command)
