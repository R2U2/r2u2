from .ast import *

def rewrite_extended_operators(program: Program) -> None:
    """
    Rewrites program formulas without extended operators i.e., formulas with only negation, conjunction, until, global, and future.

    Preconditions:
        - program is type correct.

    Postconditions:
        - program formulas only have negation, conjunction, until, and global TL operators.
    """

    if not program.is_type_correct:
        logger.error(f' Program must be type checked before rewriting.')
        return

    def rewrite_extended_operators_util(node: Node) -> None:

        if isinstance(node, LogicalOperator):
            if isinstance(node, LogicalOr):
                # p || q = !(!p && !q)
                node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [LogicalNegate(c.ln, c) for c in node.get_children()])))
            elif isinstance(node, LogicalXor):
                lhs: Node = node.get_lhs()
                rhs: Node = node.get_rhs()
                # p xor q = (p && !q) || (!p && q) = !(!(p && !q) && !(!p && q))
                node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [LogicalNegate(node.ln, \
                    LogicalAnd(node.ln, [lhs, LogicalNegate(rhs.ln, rhs)])), LogicalNegate(node.ln, \
                        LogicalAnd(node.ln, [LogicalNegate(lhs.ln, lhs), rhs]))])))
            elif isinstance(node, LogicalImplies):
                lhs: Node = node.get_lhs()
                rhs: Node = node.get_rhs()
                # p -> q = !(p && !q)
                node.replace(LogicalNegate(node.ln, LogicalAnd(lhs.ln, [lhs, LogicalNegate(rhs.ln, rhs)])))
            elif isinstance(node, LogicalIff):
                lhs: Node = node.get_lhs()
                rhs: Node = node.get_rhs()
                # p <-> q = !(p && !q) && !(p && !q)
                node.replace(LogicalAnd(node.ln,
                    [LogicalNegate(node.ln, LogicalAnd(lhs.ln, [lhs, LogicalNegate(rhs.ln, rhs)])),
                     LogicalNegate(node.ln, LogicalAnd(lhs.ln, [LogicalNegate(lhs.ln, lhs), rhs]))])
                )
        elif isinstance(node, Release):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            bounds: Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(LogicalNegate(node.ln, Until(node.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))
        elif isinstance(node, Future):
            operand: Node = node.get_operand()
            bounds: Interval = node.interval
            # F p = True U p
            node.replace(Until(node.ln, Bool(node.ln, True), operand, bounds.lb, bounds.ub))

    postorder_iterative(program, rewrite_extended_operators_util)


def rewrite_boolean_normal_form(program: Program) -> None:
    """
    Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators.

    Preconditions:
        - program is type checked

    Postconditions:
        - program formulas are in boolean normal form
    """

    if not program.is_type_correct:
        logger.error(f' Program must be type checked before converting to boolean normal form.')
        return

    def rewrite_boolean_normal_form_util(node: Node) -> None:

        if isinstance(node, LogicalOr):
            # p || q = !(!p && !q)
            node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [LogicalNegate(c.ln, c) for c in node.get_children()])))
        elif isinstance(node, LogicalImplies):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p -> q = !(p && !q)
            node.replace(LogicalNegate(node.ln, LogicalAnd(node.ln, [lhs, LogicalNegate(rhs.ln, rhs)])))
        elif isinstance(node, LogicalXor):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p xor q = !(!p && !q) && !(p && q)
            node.replace(LogicalAnd(node.ln, [LogicalNegate(node.ln, LogicalAnd(lhs.ln, [LogicalNegate(lhs.ln, lhs), \
                LogicalNegate(rhs.ln, rhs)])), LogicalNegate(lhs.ln, LogicalAnd(lhs.ln, [lhs, rhs]))]))
        elif isinstance(node, Future):
            operand: Node = node.get_operand()
            bounds: Interval = node.interval
            # F p = True U p
            node.replace(Until(node.ln, Bool(operand.ln, True), operand, bounds.lb, bounds.ub))
        elif isinstance(node, Global):
            operand: Node = node.get_operand()
            bounds: Interval = node.interval
            # G p = !(True U !p)
            node.replace(LogicalNegate(node.ln, Until(node.ln, Bool(operand.ln, True), LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub)))
        elif isinstance(node, Release):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            bounds: Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(LogicalNegate(node.ln, Until(node.ln, LogicalNegate(lhs.ln, lhs), \
                                                      LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))

        for child in node.get_children():
            rewrite_boolean_normal_form_util(child)

    rewrite_boolean_normal_form_util(program)


def rewrite_negative_normal_form(program: Program) -> None:
    """
    Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals.

    Preconditions:
        - program is type checked

    Postconditions:
        - program formulas are in negative normal form
    """

    if not program.is_type_correct:
        logger.error(f' Program must be type checked before converting to negative normal form.')
        return

    def rewrite_negative_normal_form_util(node: Node) -> None:

        if isinstance(node, LogicalNegate):
            operand = node.get_operand()
            if isinstance(operand, LogicalNegate):
                # !!p = p
                node.replace(operand.get_operand())
            if isinstance(operand, LogicalOr):
                # !(p || q) = !p && !q
                node.replace(LogicalAnd(node.ln, [LogicalNegate(c.ln, c) for c in operand.get_children()]))
            if isinstance(operand, LogicalAnd):
                # !(p && q) = !p || !q
                node.replace(LogicalOr(node.ln, [LogicalNegate(c.ln, c) for c in operand.get_children()]))
            elif isinstance(operand, Future):
                bounds: Interval = operand.interval
                # !F p = G !p
                node.replace(Global(node.ln, LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, Global):
                bounds: Interval = operand.interval
                # !G p = F !p
                node.replace(Future(node.ln, LogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, Until):
                lhs: Node = operand.get_lhs()
                rhs: Node = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p U q) = !p R !q
                node.replace(Release(node.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
            elif isinstance(operand, Release):
                lhs: Node = operand.get_lhs()
                rhs: Node = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p R q) = !p U !q
                node.replace(Until(node.ln, LogicalNegate(lhs.ln, lhs), LogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
        elif isinstance(node, LogicalImplies):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p -> q = !p || q
            node.replace(LogicalOr(node.ln, [LogicalNegate(lhs.ln, lhs), rhs]))
        elif isinstance(node, LogicalXor):
            lhs: Node = node.get_lhs()
            rhs: Node = node.get_rhs()
            # p xor q = (p && !q) || (!p && q)
            node.replace(LogicalOr(node.ln, [LogicalAnd(node.ln, [lhs, LogicalNegate(rhs.ln, rhs)]),\
                                       LogicalAnd(node.ln, [LogicalNegate(lhs.ln, lhs), rhs])]))

        for child in node.get_children():
            rewrite_negative_normal_form_util(child)

    rewrite_negative_normal_form_util(program)


def rewrite_set_aggregation(program: Program) -> None:
    """
    Rewrites set aggregation operators into corresponding BZ and TL operations e.g., foreach is rewritten into a conjunction.

    Preconditions:
        - program is type correct

    Postconditions:
        - program has no struct access operations
        - program has no variables
    """

    # could be done far more efficiently...currently traverses each set agg
    # expression sub tree searching for struct accesses. better approach: keep
    # track of these accesses on the frontend
    def rewrite_struct_access_util(node: Node) -> None:
        for c in node.get_children():
            rewrite_struct_access_util(c)

        if isinstance(node,StructAccess) and not isinstance(node.get_struct(),Variable):
            s: Struct = node.get_struct()
            node.replace(s.members[node.member])

    def rewrite_set_aggregation_util(a: Node) -> None:
        cur: Node = a

        if isinstance(a, ForEach):
            rewrite_struct_access_util(a.get_set())
            cur = LogicalAnd(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()])
            a.replace(cur) 
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForSome):
            rewrite_struct_access_util(a.get_set())
            cur = LogicalOr(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()])
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForExactlyN):
            s: Set = a.get_set()
            rewrite_struct_access_util(a.get_set())
            cur = Equal(a.ln, ArithmeticAdd(a.ln, [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.num)
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForAtLeastN):
            s: Set = a.get_set()
            rewrite_struct_access_util(s)
            cur = GreaterThanOrEqual(a.ln, ArithmeticAdd(a.ln, [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.num)
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, ForAtMostN):
            s: Set = a.get_set()
            rewrite_struct_access_util(s)
            cur = LessThanOrEqual(a.ln, ArithmeticAdd(a.ln, [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.num)
            a.replace(cur)
            rewrite_struct_access_util(cur)

        for c in cur.get_children():
            rewrite_set_aggregation_util(c)

    rewrite_set_aggregation_util(program)
    program.is_set_agg_free = True


def rewrite_struct_access(program: Program) -> None:
    """
    Rewrites struct access operations to the references member expression.

    Preconditions:
        - program is type correct
        - program has no set aggregation operators

    Postconditions:
        - program has no struct access operations
    """

    if not program.is_type_correct:
        logger.error(f' Program must be type checked before rewriting struct accesses.')
        return
    if not program.is_set_agg_free:
        logger.error(f' Program must be free of set aggregation operators before rewriting struct accesses.')
        return

    def rewrite_struct_access_util(node: Node) -> None:
        if isinstance(node, StructAccess):
            s: Struct = node.get_struct()
            node.replace(s.members[node.member])

    postorder_iterative(program, rewrite_struct_access_util)
    program.is_struct_access_free = True


def optimize_rewrite_rules(program: Node) -> None:

    def optimize_rewrite_rules_util(node: Node) -> None:
        if isinstance(node, LogicalNegate):
            opnd1 = node.get_operand()
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # !true = false
                    node.replace(Bool(node.ln, False))
                else:
                    # !false = true
                    node.replace(Bool(node.ln, True))
            elif isinstance(opnd1, LogicalNegate):
                # !!p = p
                node.replace(opnd1.get_operand())
            elif isinstance(opnd1, Global):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    node.replace(Future(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
            elif isinstance(opnd1, Future):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, LogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    node.replace(Global(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
        elif isinstance(node, Equal):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(lhs, Bool) and isinstance(rhs, Bool):
                pass
            elif isinstance(lhs, Bool):
                # (true == p) = p
                node.replace(rhs)
            elif isinstance(rhs, Bool):
                # (p == true) = p
                node.replace(lhs)
        elif isinstance(node, Global):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # G[0,0]p = p
                node.replace(opnd1)
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # G[l,u]True = True
                    node.replace(Bool(node.ln, True))
                else:
                    # G[l,u]False = False
                    node.replace(Bool(node.ln, False))
            elif isinstance(opnd1, Global):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                node.replace(Global(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, Future):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    node.replace(Future(node.ln, opnd2, lb, ub))
        elif isinstance(node, Future):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # F[0,0]p = p
                node.replace(opnd1)
            if isinstance(opnd1, Bool):
                if opnd1.value == True:
                    # F[l,u]True = True
                    node.replace(Bool(node.ln, True))
                else:
                    # F[l,u]False = False
                    node.replace(Bool(node.ln, False))
            elif isinstance(opnd1, Future):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                node.replace(Future(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, Global):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    node.replace(Global(node.ln, opnd2, lb, ub))
        elif isinstance(node, LogicalAnd):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
            if isinstance(lhs, Global) and isinstance(rhs, Global):
                p = lhs.get_operand()
                q = rhs.get_operand()
                lb1: int = lhs.interval.lb
                ub1: int = lhs.interval.ub
                lb2: int = rhs.interval.lb
                ub2: int = rhs.interval.ub

                if str(p) == str(q): # check syntactic equivalence
                    # G[lb1,lb2]p && G[lb2,ub2]p
                    if lb1 <= lb2 and ub1 >= ub2:
                        # lb1 <= lb2 <= ub2 <= ub1
                        node.replace(Global(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        node.replace(Global(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        node.replace(Global(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        node.replace(Global(node.ln, p, lb2, max(ub1,ub2)))
                        return

                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                node.replace(Global(node.ln, LogicalAnd(node.ln,
                        [Global(node.ln, p, lb1-lb3, ub1-ub3), Global(node.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
            elif isinstance(lhs, Future) and isinstance(rhs, Future):
                lhs_opnd = lhs.get_operand()
                rhs_opnd = rhs.get_operand()
                if str(lhs_opnd) == str(rhs_opnd): # check for syntactic equivalence
                    # F[l1,u1]p && F[l2,u2]p = F[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and lb1 <= ub2:
                        # l2 <= l1 <= u2
                        node.replace(Future(node.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        node.replace(Future(node.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    node.replace(Until(node.ln, LogicalAnd(node.ln, [lhs_lhs, rhs_lhs]), lhs_rhs, lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(node, LogicalOr):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
            if isinstance(lhs, Future) and isinstance(rhs, Future):
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
                        node.replace(Future(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        node.replace(Future(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        node.replace(Future(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        node.replace(Future(node.ln, p, lb2, max(ub1,ub2)))
                        return

                # TODO: check for when lb==ub==0
                # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                node.replace(Future(node.ln, LogicalOr(node.ln,
                        [Future(node.ln, p, lb1-lb3, ub1-ub3), Future(node.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
            elif isinstance(lhs, Global) and isinstance(rhs, Global):
                lhs_opnd = lhs.get_operand()
                rhs_opnd = rhs.get_operand()
                if str(lhs_opnd) == str(rhs_opnd):
                    # G[l1,u1]p || G[l2,u2]p = G[max(l1,l2),min(u1,u2)]p
                    lb1 = lhs.interval.lb
                    ub1 = lhs.interval.ub
                    lb2 = rhs.interval.lb
                    ub2 = rhs.interval.ub
                    if lb1 >= lb2 and lb1 <= ub2:
                        # l2 <= l1 <= u2
                        node.replace(Global(node.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        node.replace(Global(node.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, Until) and isinstance(rhs, Until):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    node.replace(Until(node.ln, LogicalOr(node.ln, [lhs_rhs, rhs_rhs]), lhs_lhs, lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(node, Until):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(rhs, Global) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                node.replace(Global(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))
            elif isinstance(rhs, Future) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                node.replace(Future(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))

    postorder_iterative(program, optimize_rewrite_rules_util)


def optimize_stratify_associative_operators(node: Node) -> None:
    """TODO"""

    def optimize_associative_operators_rec(node: Node) -> None:
        if isinstance(node, LogicalAnd) and len(node.get_children()) > 2:
            n: int = len(node.get_children())
            children = [c for c in node.get_children()]
            wpds = [c.wpd for c in children]
            wpds.sort(reverse=True)

            T = max(children, key=lambda c: c.wpd)

            if (n-2)*(wpds[0]-wpds[1])-wpds[2]+min([c.bpd for c in node.get_children() if c.wpd < wpds[0]]):
                node.replace(LogicalAnd(node.ln, [LogicalAnd(node.ln, [c for c in children if c != children[0]]), children[0]]))
                children[0].get_parents().remove(node)

        elif isinstance(node, LogicalOr):
            max_wpd: int = max([c.wpd for c in node.get_children()])
            target: Node = next(c for c in node.get_children() if c.wpd == max_wpd)

            new_children = [c for c in node.get_children() if c != target]
            new_ast = LogicalOr(node.ln, [LogicalOr(node.ln, new_children), target])

        for c in node.get_children():
            optimize_associative_operators_rec(c)

    optimize_associative_operators_rec(node)


def rewrite_contracts(program: Program) -> None:
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""

    for spec_set in program.get_children():
        for contract in [c for c in spec_set.get_children() if isinstance(c, Contract)]:
            spec_set.remove_child(contract)

            spec_set.add_child(Specification(
                contract.ln,
                contract.name,
                contract.formula_numbers[0],
                contract.get_assumption()
            ))

            spec_set.add_child(Specification(
                contract.ln,
                contract.name,
                contract.formula_numbers[1],
                LogicalImplies(contract.ln, contract.get_assumption(), contract.get_guarantee())
            ))

            spec_set.add_child(Specification(
                contract.ln,
                contract.name,
                contract.formula_numbers[2],
                LogicalAnd(contract.ln, [contract.get_assumption(), contract.get_guarantee()])
            ))

            program.contracts[contract.name] = contract.formula_numbers