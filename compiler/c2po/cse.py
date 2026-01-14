from typing import Any
from c2po import cpt, log, command

def optimize_cse(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Performs syntactic common sub-expression elimination (CSE) on program. 
    Uses string representation of each sub-expression to determine syntactic equivalence. 
    Applies CSE to FT/PT formulas separately.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    expr_map: dict[str, cpt.Expression]

    def _optimize_cse(expr: cpt.Expression) -> None:
        nonlocal expr_map

        if repr(expr) in expr_map:
            log.debug(2, f"replacing -- {repr(expr)} -> {id(expr_map[repr(expr)])}")
            expr.replace(expr_map[repr(expr)])
        else:
            log.debug(2, f"visiting --- {repr(expr)} -> {id(expr)}")
            expr_map[repr(expr)] = expr

    expr_map = {}
    for expr in cpt.postorder(program.ft_spec_set, context):
        _optimize_cse(expr)

    expr_map = {}
    for expr in cpt.postorder(program.pt_spec_set, context):
        _optimize_cse(expr)

    log.debug(1, f"post CSE:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

optimize_cse_command = command.Command(
    name="optimize_cse",
    description="Performs syntactic common sub-expression elimination on program. Applies CSE to FT/PT formulas separately.",
    options=[],
    func=optimize_cse,
    guards=[command.DESUGARED],
)
command.CommandRegistry.register(optimize_cse_command)
