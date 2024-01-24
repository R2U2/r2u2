from __future__ import annotations
from typing import cast, Optional, Callable

from c2po import log
from c2po import types
from c2po import cpt


def transform_definitions(program: cpt.Program, context: cpt.Context) -> None:
    """Transforms each definition symbol in the definitions and specifications of `program` to its expanded definition. This is essentially macro expansion."""

    def _transform_definitions(node: cpt.Node):
        if isinstance(node, cpt.Variable):
            if node.symbol in context.definitions:
                node.replace(context.definitions[node.symbol])
            elif node.symbol in context.specifications:
                node.replace(context.specifications[node.symbol].get_expr())

    for node in [n for d in context.definitions.values() for n in cpt.postorder(d)]:
        _transform_definitions(node)

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _transform_definitions(node)


def transform_function_calls(
    program: cpt.Program, context: cpt.Context
) -> None:
    """Transforms each function call in `program` that corresponds to a struct instantiation to a `ast.C2POStruct`."""

    def _transform_function_calls(node: cpt.Node) -> None:
        if isinstance(node, cpt.FunctionCall) and node.symbol in context.structs:
            struct_members = [m for m in context.structs[node.symbol].keys()]
            node.replace(
                cpt.Struct(
                    node.loc,
                    node.symbol,
                    {
                        name: struct_members.index(name)
                        for name in context.structs[node.symbol].keys()
                    },
                    cast("list[cpt.Node]", node.children),
                )
            )

    for node in [n for d in context.definitions.values() for n in cpt.postorder(d)]:
        _transform_function_calls(node)

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _transform_function_calls(node)


def transform_contracts(program: cpt.Program, context: cpt.Context) -> None:
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""

    for spec_section in program.get_spec_sections():
        for contract in [
            c for c in spec_section.children if isinstance(c, cpt.Contract)
        ]:
            spec_section.remove_child(contract)

            spec_section.add_child(
                cpt.Specification(
                    contract.loc,
                    contract.symbol,
                    contract.formula_numbers[0],
                    contract.get_assumption(),
                )
            )

            spec_section.add_child(
                cpt.Specification(
                    contract.loc,
                    contract.symbol,
                    contract.formula_numbers[1],
                    cpt.LogicalImplies(
                        contract.loc, contract.get_assumption(), contract.get_guarantee()
                    ),
                )
            )

            spec_section.add_child(
                cpt.Specification(
                    contract.loc,
                    contract.symbol,
                    contract.formula_numbers[2],
                    cpt.LogicalAnd(
                        contract.loc,
                        [contract.get_assumption(), contract.get_guarantee()],
                    ),
                )
            )


def transform_set_aggregation(
    program: cpt.Program, context: cpt.Context
) -> None:
    """Transforms set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction."""

    def _transform_struct_access(node: cpt.Node) -> None:
        if isinstance(node, cpt.StructAccess) and not isinstance(
            node.get_struct(), cpt.Variable
        ):
            s: cpt.Struct = node.get_struct()
            member = s.get_member(node.member)
            if member:
                node.replace(member)

    def _transform_set_aggregation(node: cpt.Node) -> None:
        cur: cpt.Node = node

        if isinstance(node, cpt.ForEach):
            for _node in cpt.postorder(node.get_set()):
                _transform_struct_access(_node)

            cur = cpt.LogicalAnd(
                node.loc,
                [
                    cpt.rename(node.get_boundvar(), e, node.get_expr())
                    for e in node.get_set().children
                ],
            )

            node.replace(cur)
        elif isinstance(node, cpt.ForSome):
            _transform_struct_access(node.get_set())
            cur = cpt.LogicalOr(
                node.loc,
                [
                    cpt.rename(node.get_boundvar(), e, node.get_expr())
                    for e in node.get_set().children
                ],
            )
            node.replace(cur)
            _transform_struct_access(cur)
        elif isinstance(node, cpt.ForExactly):
            s: cpt.SetExpression = node.get_set()
            _transform_struct_access(node.get_set())
            cur = cpt.Equal(
                node.loc,
                cpt.ArithmeticAdd(
                    node.loc,
                    [
                        cpt.rename(node.get_boundvar(), e, node.get_expr())
                        for e in node.get_set().children
                    ],
                ),
                node.get_num(),
            )
            node.replace(cur)
            _transform_struct_access(cur)
        elif isinstance(node, cpt.ForAtLeast):
            s: cpt.SetExpression = node.get_set()
            _transform_struct_access(s)
            cur = cpt.GreaterThanOrEqual(
                node.loc,
                cpt.ArithmeticAdd(
                    node.loc,
                    [
                        cpt.rename(node.get_boundvar(), e, node.get_expr())
                        for e in node.get_set().children
                    ],
                ),
                node.get_num(),
            )
            node.replace(cur)
            _transform_struct_access(cur)
        elif isinstance(node, cpt.ForAtMost):
            s: cpt.SetExpression = node.get_set()
            _transform_struct_access(s)
            cur = cpt.LessThanOrEqual(
                node.loc,
                cpt.ArithmeticAdd(
                    node.loc,
                    [
                        cpt.rename(node.get_boundvar(), e, node.get_expr())
                        for e in node.get_set().children
                    ],
                ),
                node.get_num(),
            )
            node.replace(cur)
            _transform_struct_access(cur)

        for c in cur.children:
            _transform_set_aggregation(c)

    for spec_section in program.get_spec_sections():
        _transform_set_aggregation(spec_section)


def transform_struct_accesses(
    program: cpt.Program, context: cpt.Context
) -> None:
    """Transforms struct access operations to the underlying member expression."""

    def _transform_struct_accesses(node: cpt.Node):
        if isinstance(node, cpt.StructAccess):
            s: cpt.Struct = node.get_struct()
            member = s.get_member(node.member)
            if member:
                node.replace(member)

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _transform_struct_accesses(node)


def transform_extended_operators(
    program: cpt.Program, context: cpt.Context
) -> None:
    """Transforms specifications in `program` to remove extended operators (or, xor, implies, iff, release, future)."""

    def _transform_extended_operators(node: cpt.Node):
        if isinstance(node, cpt.LogicalOperator):
            if isinstance(node, cpt.LogicalOr):
                # p || q = !(!p && !q)
                node.replace(
                    cpt.LogicalNegate(
                        node.loc,
                        cpt.LogicalAnd(
                            node.loc,
                            [cpt.LogicalNegate(c.loc, c) for c in node.children],
                        ),
                    )
                )
            elif isinstance(node, cpt.LogicalXor):
                lhs: cpt.Node = node.get_lhs()
                rhs: cpt.Node = node.get_rhs()
                # p xor q = (p && !q) || (!p && q) = !(!(p && !q) && !(!p && q))
                node.replace(
                    cpt.LogicalNegate(
                        node.loc,
                        cpt.LogicalAnd(
                            node.loc,
                            [
                                cpt.LogicalNegate(
                                    node.loc,
                                    cpt.LogicalAnd(
                                        node.loc,
                                        [lhs, cpt.LogicalNegate(rhs.loc, rhs)],
                                    ),
                                ),
                                cpt.LogicalNegate(
                                    node.loc,
                                    cpt.LogicalAnd(
                                        node.loc,
                                        [cpt.LogicalNegate(lhs.loc, lhs), rhs],
                                    ),
                                ),
                            ],
                        ),
                    )
                )
            elif isinstance(node, cpt.LogicalImplies):
                lhs: cpt.Node = node.get_lhs()
                rhs: cpt.Node = node.get_rhs()
                # p -> q = !(p && !q)
                node.replace(
                    cpt.LogicalNegate(
                        node.loc,
                        cpt.LogicalAnd(
                            lhs.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]
                        ),
                    )
                )
            elif isinstance(node, cpt.LogicalIff):
                lhs: cpt.Node = node.get_lhs()
                rhs: cpt.Node = node.get_rhs()
                # p <-> q = !(p && !q) && !(p && !q)
                node.replace(
                    cpt.LogicalAnd(
                        node.loc,
                        [
                            cpt.LogicalNegate(
                                node.loc,
                                cpt.LogicalAnd(
                                    lhs.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]
                                ),
                            ),
                            cpt.LogicalNegate(
                                node.loc,
                                cpt.LogicalAnd(
                                    lhs.loc, [cpt.LogicalNegate(lhs.loc, lhs), rhs]
                                ),
                            ),
                        ],
                    )
                )
        elif isinstance(node, cpt.Release):
            lhs: cpt.Node = node.get_lhs()
            rhs: cpt.Node = node.get_rhs()
            bounds: types.Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(
                cpt.LogicalNegate(
                    node.loc,
                    cpt.Until(
                        node.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    ),
                )
            )
        elif isinstance(node, cpt.Future):
            operand: cpt.Node = node.get_operand()
            bounds: types.Interval = node.interval
            # F p = True U p
            node.replace(
                cpt.Until(
                    node.loc, cpt.Bool(node.loc, True), operand, bounds.lb, bounds.ub
                )
            )

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _transform_extended_operators(node)


def transform_boolean_normal_form(
    program: cpt.Program, context: cpt.Context
) -> None:
    """Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators."""

    def _transform_boolean_normal_form(node: cpt.Node) -> None:
        if isinstance(node, cpt.LogicalOr):
            # p || q = !(!p && !q)
            node.replace(
                cpt.LogicalNegate(
                    node.loc,
                    cpt.LogicalAnd(
                        node.loc, [cpt.LogicalNegate(c.loc, c) for c in node.children]
                    ),
                )
            )
        elif isinstance(node, cpt.LogicalImplies):
            lhs: cpt.Node = node.get_lhs()
            rhs: cpt.Node = node.get_rhs()
            # p -> q = !(p && !q)
            node.replace(
                cpt.LogicalNegate(
                    node.loc,
                    cpt.LogicalAnd(
                        node.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]
                    ),
                )
            )
        elif isinstance(node, cpt.LogicalXor):
            lhs: cpt.Node = node.get_lhs()
            rhs: cpt.Node = node.get_rhs()
            # p xor q = !(!p && !q) && !(p && q)
            node.replace(
                cpt.LogicalAnd(
                    node.loc,
                    [
                        cpt.LogicalNegate(
                            node.loc,
                            cpt.LogicalAnd(
                                lhs.loc,
                                [
                                    cpt.LogicalNegate(lhs.loc, lhs),
                                    cpt.LogicalNegate(rhs.loc, rhs),
                                ],
                            ),
                        ),
                        cpt.LogicalNegate(
                            lhs.loc, cpt.LogicalAnd(lhs.loc, [lhs, rhs])
                        ),
                    ],
                )
            )
        elif isinstance(node, cpt.Future):
            operand: cpt.Node = node.get_operand()
            bounds: types.Interval = node.interval
            # F p = True U p
            node.replace(
                cpt.Until(
                    node.loc,
                    cpt.Bool(operand.loc, True),
                    operand,
                    bounds.lb,
                    bounds.ub,
                )
            )
        elif isinstance(node, cpt.Global):
            operand: cpt.Node = node.get_operand()
            bounds: types.Interval = node.interval
            # G p = !(True U !p)
            node.replace(
                cpt.LogicalNegate(
                    node.loc,
                    cpt.Until(
                        node.loc,
                        cpt.Bool(operand.loc, True),
                        cpt.LogicalNegate(operand.loc, operand),
                        bounds.lb,
                        bounds.ub,
                    ),
                )
            )
        elif isinstance(node, cpt.Release):
            lhs: cpt.Node = node.get_lhs()
            rhs: cpt.Node = node.get_rhs()
            bounds: types.Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(
                cpt.LogicalNegate(
                    node.loc,
                    cpt.Until(
                        node.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    ),
                )
            )

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _transform_boolean_normal_form(node)


def transform_negative_normal_form(
    program: cpt.Program, context: cpt.Context
) -> None:
    """Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals."""

    def _transform_negative_normal_form(node: cpt.Node) -> None:
        if isinstance(node, cpt.LogicalNegate):
            operand = node.get_operand()
            if isinstance(operand, cpt.LogicalNegate):
                # !!p = p
                node.replace(operand.get_operand())
            if isinstance(operand, cpt.LogicalOr):
                # !(p || q) = !p && !q
                node.replace(
                    cpt.LogicalAnd(
                        node.loc,
                        [cpt.LogicalNegate(c.loc, c) for c in operand.children],
                    )
                )
            if isinstance(operand, cpt.LogicalAnd):
                # !(p && q) = !p || !q
                node.replace(
                    cpt.LogicalOr(
                        node.loc,
                        [cpt.LogicalNegate(c.loc, c) for c in operand.children],
                    )
                )
            elif isinstance(operand, cpt.Future):
                bounds: types.Interval = operand.interval
                # !F p = G !p
                node.replace(
                    cpt.Global(
                        node.loc,
                        cpt.LogicalNegate(operand.loc, operand),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Global):
                bounds: types.Interval = operand.interval
                # !G p = F !p
                node.replace(
                    cpt.Future(
                        node.loc,
                        cpt.LogicalNegate(operand.loc, operand),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Until):
                lhs: cpt.Node = operand.get_lhs()
                rhs: cpt.Node = operand.get_rhs()
                bounds: types.Interval = operand.interval
                # !(p U q) = !p R !q
                node.replace(
                    cpt.Release(
                        node.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    )
                )
            elif isinstance(operand, cpt.Release):
                lhs: cpt.Node = operand.get_lhs()
                rhs: cpt.Node = operand.get_rhs()
                bounds: types.Interval = operand.interval
                # !(p R q) = !p U !q
                node.replace(
                    cpt.Until(
                        node.loc,
                        cpt.LogicalNegate(lhs.loc, lhs),
                        cpt.LogicalNegate(rhs.loc, rhs),
                        bounds.lb,
                        bounds.ub,
                    )
                )
        elif isinstance(node, cpt.LogicalImplies):
            lhs: cpt.Node = node.get_lhs()
            rhs: cpt.Node = node.get_rhs()
            # p -> q = !p || q
            node.replace(
                cpt.LogicalOr(node.loc, [cpt.LogicalNegate(lhs.loc, lhs), rhs])
            )
        elif isinstance(node, cpt.LogicalXor):
            lhs: cpt.Node = node.get_lhs()
            rhs: cpt.Node = node.get_rhs()
            # p xor q = (p && !q) || (!p && q)
            node.replace(
                cpt.LogicalOr(
                    node.loc,
                    [
                        cpt.LogicalAnd(
                            node.loc, [lhs, cpt.LogicalNegate(rhs.loc, rhs)]
                        ),
                        cpt.LogicalAnd(
                            node.loc, [cpt.LogicalNegate(lhs.loc, lhs), rhs]
                        ),
                    ],
                )
            )

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _transform_negative_normal_form(node)


def optimize_rewrite_rules(program: cpt.Program, context: cpt.Context) -> None:
    """Applies MLTL rewrite rules to reduce required SCQ memory."""

    def _optimize_rewrite_rules(node: cpt.Node) -> None:
        new: Optional[cpt.Node] = None

        if isinstance(node, cpt.LogicalNegate):
            opnd1 = node.get_operand()
            if isinstance(opnd1, cpt.Bool):
                if opnd1.value is True:
                    # !true = false
                    new = cpt.Bool(node.loc, False)
                else:
                    # !false = true
                    new = cpt.Bool(node.loc, True)
            elif isinstance(opnd1, cpt.LogicalNegate):
                # !!p = p
                new = opnd1.get_operand()
            elif isinstance(opnd1, cpt.Global):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, cpt.LogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    new = cpt.Future(
                        node.loc,
                        opnd2.get_operand(),
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                    )
            elif isinstance(opnd1, cpt.Future):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, cpt.LogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    new = cpt.Global(
                        node.loc,
                        opnd2.get_operand(),
                        opnd1.interval.lb,
                        opnd1.interval.ub,
                    )
        elif isinstance(node, cpt.Equal):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(lhs, cpt.Bool) and isinstance(rhs, cpt.Bool):
                pass
            elif isinstance(lhs, cpt.Bool):
                # (true == p) = p
                new = rhs
            elif isinstance(rhs, cpt.Bool):
                # (p == true) = p
                new = lhs
        elif isinstance(node, cpt.Global):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # G[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Bool):
                if opnd1.value is True:
                    # G[l,u]True = True
                    new = cpt.Bool(node.loc, True)
                else:
                    # G[l,u]False = False
                    new = cpt.Bool(node.loc, False)
            elif isinstance(opnd1, cpt.Global):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                new = cpt.Global(node.loc, opnd2, lb, ub)
            elif isinstance(opnd1, cpt.Future):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    new = cpt.Future(node.loc, opnd2, lb, ub)
        elif isinstance(node, cpt.Future):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # F[0,0]p = p
                new = opnd1
            if isinstance(opnd1, cpt.Bool):
                if opnd1.value is True:
                    # F[l,u]True = True
                    new = cpt.Bool(node.loc, True)
                else:
                    # F[l,u]False = False
                    new = cpt.Bool(node.loc, False)
            elif isinstance(opnd1, cpt.Future):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                new = cpt.Future(node.loc, opnd2, lb, ub)
            elif isinstance(opnd1, cpt.Global):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    new = cpt.Global(node.loc, opnd2, lb, ub)
        elif isinstance(node, cpt.LogicalAnd):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
            if isinstance(lhs, cpt.Global) and isinstance(rhs, cpt.Global):
                p = lhs.get_operand()
                q = rhs.get_operand()
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q):  # check syntactic equivalence
                    # G[lb1,lb2]p && G[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.Global(node.loc, p, lb1, ub1)
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.Global(node.loc, p, lb2, ub2)
                        return
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.Global(node.loc, p, lb1, max(ub1, ub2))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.Global(node.loc, p, lb2, max(ub1, ub2))
                        return

                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1 - lb1, ub2 - lb2)

                new = cpt.Global(
                    node.loc,
                    cpt.LogicalAnd(
                        node.loc,
                        [
                            cpt.Global(node.loc, p, lb1 - lb3, ub1 - ub3),
                            cpt.Global(node.loc, q, lb2 - lb3, ub2 - ub3),
                        ],
                    ),
                    lb3,
                    ub3,
                )
            elif isinstance(lhs, cpt.Future) and isinstance(rhs, cpt.Future):
                lhs_opnd = lhs.get_operand()
                rhs_opnd = rhs.get_operand()
                if str(lhs_opnd) == str(rhs_opnd):  # check for syntactic equivalence
                    # F[l1,u1]p && F[l2,u2]p = F[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and ub1 <= ub2:
                        # l2 <= l1 <= u1 <= u2
                        new = cpt.Future(node.loc, lhs_opnd, lb1, ub1)
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = cpt.Future(node.loc, lhs_opnd, lb2, ub2)
            elif isinstance(lhs, cpt.Until) and isinstance(rhs, cpt.Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    new = cpt.Until(
                        node.loc,
                        cpt.LogicalAnd(node.loc, [lhs_lhs, rhs_lhs]),
                        lhs_rhs,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                    )
        elif isinstance(node, cpt.LogicalOr):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
            if isinstance(lhs, cpt.Future) and isinstance(rhs, cpt.Future):
                p = lhs.get_operand()
                q = rhs.get_operand()
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q):
                    # F[lb1,lb2]p || F[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        new = cpt.Future(node.loc, p, lb1, ub1)
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = cpt.Future(node.loc, p, lb2, ub2)
                        return
                    elif lb1 <= lb2 and lb2 <= ub1 + 1:
                        # lb1 <= lb2 <= ub1+1
                        new = cpt.Future(node.loc, p, lb1, max(ub1, ub2))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2 + 1:
                        # lb2 <= lb1 <= ub2+1
                        new = cpt.Future(node.loc, p, lb2, max(ub1, ub2))
                        return

                # TODO: check for when lb==ub==0
                # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1 - lb1, ub2 - lb2)

                new = cpt.Future(
                    node.loc,
                    cpt.LogicalOr(
                        node.loc,
                        [
                            cpt.Future(node.loc, p, lb1 - lb3, ub1 - ub3),
                            cpt.Future(node.loc, q, lb2 - lb3, ub2 - ub3),
                        ],
                    ),
                    lb3,
                    ub3,
                )
            elif isinstance(lhs, cpt.Global) and isinstance(rhs, cpt.Global):
                lhs_opnd = lhs.get_operand()
                rhs_opnd = rhs.get_operand()
                if str(lhs_opnd) == str(rhs_opnd):
                    # G[l1,u1]p || G[l2,u2]p = G[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and ub1 <= ub2:
                        # l2 <= l1 <= u1 <= u2
                        new = cpt.Global(node.loc, lhs_opnd, lb1, ub1)
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = cpt.Global(node.loc, lhs_opnd, lb2, ub2)
            elif isinstance(lhs, cpt.Until) and isinstance(rhs, cpt.Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    new = cpt.Until(
                        node.loc,
                        cpt.LogicalOr(node.loc, [lhs_rhs, rhs_rhs]),
                        lhs_lhs,
                        lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub),
                    )
        elif isinstance(node, cpt.Until):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if (
                isinstance(rhs, cpt.Global)
                and rhs.interval.lb == 0
                and str(lhs) == str(rhs.get_operand())
            ):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                new = cpt.Global(
                    node.loc, lhs, node.interval.lb, node.interval.lb + rhs.interval.ub
                )
            elif (
                isinstance(rhs, cpt.Future)
                and rhs.interval.lb == 0
                and str(lhs) == str(rhs.get_operand())
            ):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                new = cpt.Future(
                    node.loc, lhs, node.interval.lb, node.interval.lb + rhs.interval.ub
                )

        if new:
            log.debug(f"REWRITE:\n\t{node}\n\t\t===>\n\t{new}", __name__)
            node.replace(new)

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _optimize_rewrite_rules(node)


def optimize_cse(program: cpt.Program, context: cpt.Context) -> None:
    """Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence. Applies CSE to FT/PT formulas separately."""
    S: dict[str, cpt.Node]

    log.debug("CSE: Beginning CSE", __name__)

    def _optimize_cse(node: cpt.Node) -> None:
        nonlocal S

        if str(node) in S:
            log.debug(f"CSE: Replacing --- {node}", __name__)
            node.replace(S[str(node)])
        else:
            log.debug(f"CSE: Visiting ---- {node}", __name__)
            S[str(node)] = node

    for spec_section in program.get_spec_sections():
        S = {}
        for node in cpt.postorder(spec_section):
            _optimize_cse(node)


def compute_atomics(program: cpt.Program, context: cpt.Context) -> None:
    """Compute atomics and store them in `context`. An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine."""
    id: int = 0

    def _compute_atomics(node: cpt.Node):
        nonlocal id

        if not isinstance(node, cpt.Expression):
            return

        if node.engine == types.R2U2Engine.TEMPORAL_LOGIC:
            return

        if isinstance(node, cpt.Bool):
            return

        for parent in [p for p in node.parents if isinstance(p, cpt.Expression)]:
            if parent.engine == types.R2U2Engine.TEMPORAL_LOGIC:
                context.atomics.add(node)
                if node.atomic_id < 0:
                    node.atomic_id = id
                    id += 1

    for node in [n for s in program.get_specs() for n in cpt.postorder(s)]:
        _compute_atomics(node)

    log.debug(
        f"ATM: Computed atomics:\n\t[{', '.join(f'({a},{a.atomic_id})' for a in context.atomics)}]",
        __name__
    )


def compute_scq_sizes(program: cpt.Program, context: cpt.Context) -> None:
    """Computes SCQ sizes for each node."""
    spec_section_total_scq_size = 0

    def _compute_scq_size(expr: cpt.Node):
        nonlocal spec_section_total_scq_size

        if not isinstance(expr, cpt.Expression):
            return

        if isinstance(expr, cpt.SpecSection):
            expr.total_scq_size = spec_section_total_scq_size
            spec_section_total_scq_size = 0
            return

        if isinstance(expr, cpt.Specification):
            expr.scq_size = 1
            expr.total_scq_size = expr.get_expr().total_scq_size + expr.scq_size
            spec_section_total_scq_size += expr.scq_size
            expr.scq = (
                spec_section_total_scq_size - expr.scq_size,
                spec_section_total_scq_size,
            )
            return

        if (
            expr.engine != types.R2U2Engine.TEMPORAL_LOGIC
            and expr not in context.atomics
        ):
            return

        max_wpd = max([sibling.wpd for sibling in expr.get_siblings()] + [0])

        # need the +3 b/c of implementation -- ask Brian
        expr.scq_size = max(max_wpd - expr.bpd, 0) + 3
        expr.total_scq_size = (
            sum([c.total_scq_size for c in expr.get_children() if c.scq_size > -1])
            + expr.scq_size
        )
        spec_section_total_scq_size += expr.scq_size

        expr.scq = (
            spec_section_total_scq_size - expr.scq_size,
            spec_section_total_scq_size,
        )

    for node in [n for s in program.get_spec_sections() for n in cpt.postorder(s)]:
        _compute_scq_size(node)


# A ast.C2POTransform is a function with the signature:
#    transform(program, context) -> None
C2POTransform = Callable[[cpt.Program, cpt.Context], None]

# Note: this is ORDER-SENSITIVE
TRANSFORM_PIPELINE: list[C2POTransform] = [
    transform_definitions,
    transform_function_calls,
    transform_contracts,
    transform_set_aggregation,
    transform_struct_accesses,
    optimize_rewrite_rules,
    transform_extended_operators,
    transform_negative_normal_form,
    transform_boolean_normal_form,
    optimize_cse,
    compute_atomics,  # not a transform, but needed for assembly+analysis
    compute_scq_sizes,  # not a transform, but needed for assembly+analysis
]
