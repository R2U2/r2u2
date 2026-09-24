from typing import Optional, cast, Any
from c2po import cpt, log, command

def optimize_rewrites(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Applies MLTL rewrite rules to reduce required SCQ memory.
    Rewrites are applied in a single pass of the expression tree.
    Returns a ReturnCode.SUCCESS if successful, ReturnCode.ERROR otherwise.
    """
    for expr in program.postorder(context):
        new: Optional[cpt.Expression] = None

        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            opnd1 = expr.children[0]
            if isinstance(opnd1, cpt.Constant):
                if opnd1.value is True:
                    # !true = false
                    new = cpt.Constant(expr.loc, False)
                else:
                    # !false = true
                    new = cpt.Constant(expr.loc, True)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.LOGICAL_NEGATE):
                # !!p = p
                new = opnd1.children[0]
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                opnd1 = cast(cpt.TemporalOperator, opnd1)

                opnd2 = opnd1.children[0]
                if cpt.is_operator(opnd2, cpt.OperatorKind.LOGICAL_NEGATE):
                    # !(G[l,u](!p)) = F[l,u]p
                    new = cpt.TemporalOperator.Future(
                        expr.loc,
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                        opnd2.children[0],
                    )
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd1 = cast(cpt.TemporalOperator, opnd1)

                opnd2 = opnd1.children[0]
                if cpt.is_operator(opnd2, cpt.OperatorKind.LOGICAL_NEGATE):
                    # !(F[l,u](!p)) = G[l,u]p
                    new = cpt.TemporalOperator.Global(
                        expr.loc,
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                        opnd2.children[0],
                    )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            lhs = expr.children[0]
            rhs = expr.children[1]
            if isinstance(lhs, cpt.Constant) and isinstance(rhs, cpt.Constant):
                pass
            elif isinstance(lhs, cpt.Constant) and isinstance(lhs.value, bool):
                # (true == p) = p
                new = rhs
            elif isinstance(rhs, cpt.Constant) and isinstance(rhs.value, bool):
                # (p == true) = p
                new = lhs
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)

            opnd1 = expr.children[0]
            if expr.interval.lb == 0 and expr.interval.ub == 0:
                # G[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Constant):
                if opnd1.value is True:
                    # G[l,u]True = True
                    new = cpt.Constant(expr.loc, True)
                else:
                    # G[l,u]False = False
                    # erroneous: the empty trace satisfies "G[l,u] False", but not "False"
                    # new = cpt.Constant(expr.loc, False)
                    pass
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb = expr.interval.lb + opnd1.interval.lb
                ub = expr.interval.ub + opnd1.interval.ub
                new = cpt.TemporalOperator.Global(expr.loc, lb, ub, opnd2)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb = expr.interval.lb + opnd1.interval.lb
                    ub = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Future(expr.loc, lb, ub, opnd2)
                elif opnd1.interval.lb == opnd1.interval.ub:
                    # G[l,u](F[a,a]p) = G[l+a,u+a]p
                    lb = expr.interval.lb + opnd1.interval.lb
                    ub = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Global(expr.loc, lb, ub, opnd2)
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)

            opnd1 = expr.children[0]
            if expr.interval.lb == 0 and expr.interval.ub == 0:
                # F[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Constant):
                if opnd1.value is True:
                    # F[l,u]True = True
                    # erroneous: the empty trace satisfies "True", but not "F[l,u] True"
                    # new = cpt.Constant(expr.loc, True)
                    pass
                else:
                    # F[l,u]False = False
                    new = cpt.Constant(expr.loc, False)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.FUTURE):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.children[0]
                lb = expr.interval.lb + opnd1.interval.lb
                ub = expr.interval.ub + opnd1.interval.ub
                new = cpt.TemporalOperator.Future(expr.loc, lb, ub, opnd2)
            elif cpt.is_operator(opnd1, cpt.OperatorKind.GLOBAL):
                opnd1 = cast(cpt.TemporalOperator, opnd1)
                opnd2 = opnd1.children[0]
                if expr.interval.lb == expr.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb = expr.interval.lb + opnd1.interval.lb
                    ub = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Global(expr.loc, lb, ub, opnd2)
                elif opnd1.interval.lb == opnd1.interval.ub:
                    # F[l,u](G[a,a]p) = F[l+a,u+a]p
                    lb = expr.interval.lb + opnd1.interval.lb
                    ub = expr.interval.ub + opnd1.interval.ub
                    new = cpt.TemporalOperator.Future(expr.loc, lb, ub, opnd2)
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if (
                cpt.is_operator(lhs, cpt.OperatorKind.GLOBAL) and 
                cpt.is_operator(rhs, cpt.OperatorKind.GLOBAL)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

                p = lhs.children[0]
                q = rhs.children[0]
                lb1 = lhs.interval.lb
                ub1 = lhs.interval.ub
                lb2 = rhs.interval.lb
                ub2 = rhs.interval.ub

                if str(p) == str(q):  # check syntactic equivalence
                    # G[lb1,lb2]p && G[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.TemporalOperator.Global(expr.loc, lb1, ub1, p)
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.TemporalOperator.Global(expr.loc,lb2, ub2, p)
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.TemporalOperator.Global(expr.loc, lb1, max(ub1, ub2), p)
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.TemporalOperator.Global(expr.loc, lb2, max(ub1, ub2), p)
                else:
                    lb3 = min(lb1, lb2)
                    ub3 = lb3 + min(ub1 - lb1, ub2 - lb2)

                    new = cpt.TemporalOperator.Global(
                        expr.loc,
                        lb3,
                        ub3,
                        cpt.Operator.LogicalAnd(
                            expr.loc,
                            [
                                cpt.TemporalOperator.Global(expr.loc, lb1 - lb3, ub1 - ub3, p),
                                cpt.TemporalOperator.Global(expr.loc, lb2 - lb3, ub2 - ub3, q),
                            ],
                        )
                    )
            elif (
                cpt.is_operator(lhs, cpt.OperatorKind.FUTURE) and 
                cpt.is_operator(rhs, cpt.OperatorKind.FUTURE)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

                lhs_opnd = lhs.children[0]
                rhs_opnd = rhs.children[0]
                if str(lhs_opnd) == str(rhs_opnd):  # check for syntactic equivalence
                    # F[l1,u1]p && F[l2,u2]p = F[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub

                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.TemporalOperator.Future(expr.loc, lb2, ub2, lhs_opnd)
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.TemporalOperator.Future(expr.loc, lb1, ub1, lhs_opnd)
            elif (
                cpt.is_operator(lhs, cpt.OperatorKind.UNTIL) and
                cpt.is_operator(rhs, cpt.OperatorKind.UNTIL)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

                lhs_lhs = lhs.children[0]
                lhs_rhs = lhs.children[1]
                rhs_lhs = rhs.children[0]
                rhs_rhs = rhs.children[1]
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    new = cpt.TemporalOperator.Until(
                        expr.loc,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                        cpt.Operator.LogicalAnd(expr.loc, [lhs_lhs, rhs_lhs]),
                        lhs_rhs
                    )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            # Assume binary for now
            lhs = expr.children[0]
            rhs = expr.children[1]
            if (
                cpt.is_operator(lhs, cpt.OperatorKind.FUTURE) and 
                cpt.is_operator(rhs, cpt.OperatorKind.FUTURE)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

                p = lhs.children[0]
                q = rhs.children[0]
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q):
                    # F[lb1,lb2]p || F[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.TemporalOperator.Future(expr.loc, lb1, ub1, p)
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.TemporalOperator.Future(expr.loc, lb2, ub2, p)
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.TemporalOperator.Future(expr.loc, lb1, max(ub1, ub2), p)
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.TemporalOperator.Future(expr.loc, lb2, max(ub1, ub2), p)
                else:
                    # TODO: check for when lb==ub==0
                    # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                    lb3 = min(lb1, lb2)
                    ub3 = lb3 + min(ub1 - lb1, ub2 - lb2)

                    new = cpt.TemporalOperator.Future(
                        expr.loc,
                        lb3,
                        ub3,
                        cpt.Operator.LogicalOr(
                            expr.loc,
                            [
                                cpt.TemporalOperator.Future(expr.loc, lb1 - lb3, ub1 - ub3, p),
                                cpt.TemporalOperator.Future(expr.loc, lb2 - lb3, ub2 - ub3, q),
                            ],
                        )
                    )
            elif (
                cpt.is_operator(lhs, cpt.OperatorKind.GLOBAL) and 
                cpt.is_operator(rhs, cpt.OperatorKind.GLOBAL)
            ):
                lhs = cast(cpt.TemporalOperator, lhs)
                rhs = cast(cpt.TemporalOperator, rhs)

                lhs_opnd = lhs.children[0]
                rhs_opnd = rhs.children[0]
                if str(lhs_opnd) == str(rhs_opnd):
                    # G[l1,u1]p || G[l2,u2]p = G[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and ub1 <= ub2:
                        # l2 <= l1 <= u1 <= u2
                        new = cpt.TemporalOperator.Global(expr.loc, lb1, ub1, lhs_opnd)
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = cpt.TemporalOperator.Global(expr.loc, lb2, ub2, lhs_opnd)

        if new:
            log.debug(
                2, f"\n\t{expr}\n\t==>\n\t{new}"
            )
            expr.replace(new)

    log.debug(1, f"post rewrite:\n{repr(program)}")
    return command.ReturnCode.SUCCESS

optimize_rewrites_command = command.Command(
    name="optimize_rewrites",
    description="Applies MLTL rewrite rules in a single pass of the expression tree to reduce required SCQ memory.",
    options=[],
    func=optimize_rewrites,
    guards=[command.DESUGARED],
)
command.CommandRegistry.register(optimize_rewrites_command)
