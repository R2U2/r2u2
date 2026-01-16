from typing import Any
from c2po import cpt, log, command, types

def compute_atomics(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Compute atomics and store them in `context`. 
    An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine.

    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    def replace_expr_parents(expr: cpt.Expression, new: cpt.Expression, parents: set[cpt.Expression]) -> None:
        """Replaces the parents of `expr` with `new` but only edits the children of the parents that are in `parents`"""
        for parent in parents:
            for i in range(0, len(parent.children)):
                if id(parent.children[i]) == id(expr):
                    parent.children[i] = new
            new.parents.add(parent)

    aid: int = 0

    for expr in program.postorder(context):
        if (
            expr.engine == types.R2U2Engine.TEMPORAL_LOGIC 
            or isinstance(expr, cpt.Constant) 
            or expr in context.atomic_id_map
        ):
            continue

        # We just cast signals as atomics when we have no frontend
        if not context.enable_booleanizer:
            if isinstance(expr, cpt.Signal):
                # If the signal id is negative it means its not in the signal mapping, so we assign
                # it a new atomic id as a temporary atomic. This will have to be resolved later if
                # the user wants to assemble the program, but we catch this in the
                # 'has_atomic_consistent_signal_mapping' check, which checks that each Signal's
                # signal ID is the same as its atomic ID.
                if expr.signal_id < 0:
                    context.atomic_id_map[expr] = aid
                    context.atomic_expr_map[aid] = expr
                    aid += 1
                else:
                    context.atomic_id_map[expr] = expr.signal_id
                    context.atomic_expr_map[expr.signal_id] = expr
        elif not isinstance(expr, cpt.Atomic):
            # add atomic node between any TL and BZ nodes
            tl_parents = {
                p for p in expr.parents if p.engine == types.R2U2Engine.TEMPORAL_LOGIC
            }

            if expr.engine != types.R2U2Engine.BOOLEANIZER or len(tl_parents) == 0:
                continue

            log.debug(2, f"adding atomic node between {repr(expr)} and {repr(tl_parents)}")
            new = cpt.Atomic(expr.loc, expr)
            replace_expr_parents(expr, new, tl_parents)

            if new in context.atomic_id_map:
                context.atomic_id_map[new] = context.atomic_id_map[new]
                context.atomic_expr_map[context.atomic_id_map[new]] = new
            else:
                context.atomic_id_map[new] = aid
                context.atomic_expr_map[aid] = new
                aid += 1

            log.debug(3, f"computed atomic: {repr(new)}")
            log.debug(3, f"new parents: {[repr(p) for p in new.parents]}")
            log.debug(3, f"new children: {[repr(c) for c in new.children]}")
            log.debug(3, f"tl parents and children: {[repr(p) for p in new.parents]} and {[repr(c) for c in new.children]}")

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
