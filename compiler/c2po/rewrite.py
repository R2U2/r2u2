from .ast import *


def rewrite_function_calls(program: C2POProgram, context: C2POContext):

    # TODO: if the node is in a definition -- need to replace the definition as well? Only if it's the top level node of the definition I think...

    def rewrite_function_calls_util(node: C2PONode):
        if isinstance(node, C2POFunctionCall) and node.symbol in context.structs:
            print(node)
            struct_members = [m for m in context.structs[node.symbol].keys()]
            node.replace(
                C2POStruct(
                    node.ln, 
                    node.symbol, 
                    {name:struct_members.index(name) for name in context.structs[node.symbol].keys()}, 
                    cast(List[C2PONode], node.get_children())
                )
            )

    for definition in context.definitions.values():
        postorder(definition, rewrite_function_calls_util)

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_function_calls_util)


def rewrite_definitions(program: C2POProgram, context: C2POContext):
    
    def rewrite_definitions_util(node: C2PONode):
        if isinstance(node, C2POVariable):
            if node.symbol in context.definitions:
                print(f"{node} : {context.definitions[node.symbol]}")
                node.replace(context.definitions[node.symbol])
            elif node.symbol in context.specifications:
                node.replace(context.specifications[node.symbol].get_expr())

    for definition in context.definitions.values():
        postorder(definition, rewrite_definitions_util)

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_definitions_util)


# TODO
def rewrite_contracts(program: C2POProgram):
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""

    for spec_set in program.get_children():
        for contract in [c for c in spec_set.get_children() if isinstance(c, C2POContract)]:
            spec_set.remove_child(contract)

            spec_set.add_child(C2POSpecification(
                contract.ln,
                contract.symbol,
                contract.formula_numbers[0],
                contract.get_assumption()
            ))

            spec_set.add_child(C2POSpecification(
                contract.ln,
                contract.symbol,
                contract.formula_numbers[1],
                C2POLogicalImplies(contract.ln, contract.get_assumption(), contract.get_guarantee())
            ))

            spec_set.add_child(C2POSpecification(
                contract.ln,
                contract.symbol,
                contract.formula_numbers[2],
                C2POLogicalAnd(contract.ln, [contract.get_assumption(), contract.get_guarantee()])
            ))

            program.contracts[contract.symbol] = contract.formula_numbers


def rewrite_extended_operators(program: C2POProgram):
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

    def rewrite_extended_operators_util(node: C2PONode):
        if isinstance(node, C2POLogicalOperator):
            if isinstance(node, C2POLogicalOr):
                # p || q = !(!p && !q)
                node.replace(C2POLogicalNegate(node.ln, C2POLogicalAnd(node.ln, [C2POLogicalNegate(c.ln, c) for c in node.get_children()])))
            elif isinstance(node, C2POLogicalXor):
                lhs: C2PONode = node.get_lhs()
                rhs: C2PONode = node.get_rhs()
                # p xor q = (p && !q) || (!p && q) = !(!(p && !q) && !(!p && q))
                node.replace(C2POLogicalNegate(node.ln, C2POLogicalAnd(node.ln, [C2POLogicalNegate(node.ln, \
                    C2POLogicalAnd(node.ln, [lhs, C2POLogicalNegate(rhs.ln, rhs)])), C2POLogicalNegate(node.ln, \
                        C2POLogicalAnd(node.ln, [C2POLogicalNegate(lhs.ln, lhs), rhs]))])))
            elif isinstance(node, C2POLogicalImplies):
                lhs: C2PONode = node.get_lhs()
                rhs: C2PONode = node.get_rhs()
                # p -> q = !(p && !q)
                node.replace(C2POLogicalNegate(node.ln, C2POLogicalAnd(lhs.ln, [lhs, C2POLogicalNegate(rhs.ln, rhs)])))
            elif isinstance(node, C2POLogicalIff):
                lhs: C2PONode = node.get_lhs()
                rhs: C2PONode = node.get_rhs()
                # p <-> q = !(p && !q) && !(p && !q)
                node.replace(C2POLogicalAnd(node.ln,
                    [C2POLogicalNegate(node.ln, C2POLogicalAnd(lhs.ln, [lhs, C2POLogicalNegate(rhs.ln, rhs)])),
                     C2POLogicalNegate(node.ln, C2POLogicalAnd(lhs.ln, [C2POLogicalNegate(lhs.ln, lhs), rhs]))])
                )
        elif isinstance(node, C2PORelease):
            lhs: C2PONode = node.get_lhs()
            rhs: C2PONode = node.get_rhs()
            bounds: Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(C2POLogicalNegate(node.ln, C2POUntil(node.ln, C2POLogicalNegate(lhs.ln, lhs), C2POLogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))
        elif isinstance(node, C2POFuture):
            operand: C2PONode = node.get_operand()
            bounds: Interval = node.interval
            # F p = True U p
            node.replace(C2POUntil(node.ln, C2POBool(node.ln, True), operand, bounds.lb, bounds.ub))

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_extended_operators_util)


def rewrite_boolean_normal_form(program: C2POProgram):
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

    def rewrite_boolean_normal_form_util(node: C2PONode):

        if isinstance(node, C2POLogicalOr):
            # p || q = !(!p && !q)
            node.replace(C2POLogicalNegate(node.ln, C2POLogicalAnd(node.ln, [C2POLogicalNegate(c.ln, c) for c in node.get_children()])))
        elif isinstance(node, C2POLogicalImplies):
            lhs: C2PONode = node.get_lhs()
            rhs: C2PONode = node.get_rhs()
            # p -> q = !(p && !q)
            node.replace(C2POLogicalNegate(node.ln, C2POLogicalAnd(node.ln, [lhs, C2POLogicalNegate(rhs.ln, rhs)])))
        elif isinstance(node, C2POLogicalXor):
            lhs: C2PONode = node.get_lhs()
            rhs: C2PONode = node.get_rhs()
            # p xor q = !(!p && !q) && !(p && q)
            node.replace(C2POLogicalAnd(node.ln, [C2POLogicalNegate(node.ln, C2POLogicalAnd(lhs.ln, [C2POLogicalNegate(lhs.ln, lhs), \
                C2POLogicalNegate(rhs.ln, rhs)])), C2POLogicalNegate(lhs.ln, C2POLogicalAnd(lhs.ln, [lhs, rhs]))]))
        elif isinstance(node, C2POFuture):
            operand: C2PONode = node.get_operand()
            bounds: Interval = node.interval
            # F p = True U p
            node.replace(C2POUntil(node.ln, C2POBool(operand.ln, True), operand, bounds.lb, bounds.ub))
        elif isinstance(node, C2POGlobal):
            operand: C2PONode = node.get_operand()
            bounds: Interval = node.interval
            # G p = !(True U !p)
            node.replace(C2POLogicalNegate(node.ln, C2POUntil(node.ln, C2POBool(operand.ln, True), C2POLogicalNegate(operand.ln, operand), bounds.lb, bounds.ub)))
        elif isinstance(node, C2PORelease):
            lhs: C2PONode = node.get_lhs()
            rhs: C2PONode = node.get_rhs()
            bounds: Interval = node.interval
            # p R q = !(!p U !q)
            node.replace(C2POLogicalNegate(node.ln, C2POUntil(node.ln, C2POLogicalNegate(lhs.ln, lhs), \
                                                      C2POLogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub)))

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_boolean_normal_form_util)


def rewrite_negative_normal_form(program: C2POProgram):
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

    def rewrite_negative_normal_form_util(node: C2PONode):

        if isinstance(node, C2POLogicalNegate):
            operand = node.get_operand()
            if isinstance(operand, C2POLogicalNegate):
                # !!p = p
                node.replace(operand.get_operand())
            if isinstance(operand, C2POLogicalOr):
                # !(p || q) = !p && !q
                node.replace(C2POLogicalAnd(node.ln, [C2POLogicalNegate(c.ln, c) for c in operand.get_children()]))
            if isinstance(operand, C2POLogicalAnd):
                # !(p && q) = !p || !q
                node.replace(C2POLogicalOr(node.ln, [C2POLogicalNegate(c.ln, c) for c in operand.get_children()]))
            elif isinstance(operand, C2POFuture):
                bounds: Interval = operand.interval
                # !F p = G !p
                node.replace(C2POGlobal(node.ln, C2POLogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, C2POGlobal):
                bounds: Interval = operand.interval
                # !G p = F !p
                node.replace(C2POFuture(node.ln, C2POLogicalNegate(operand.ln, operand), bounds.lb, bounds.ub))
            elif isinstance(operand, C2POUntil):
                lhs: C2PONode = operand.get_lhs()
                rhs: C2PONode = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p U q) = !p R !q
                node.replace(C2PORelease(node.ln, C2POLogicalNegate(lhs.ln, lhs), C2POLogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
            elif isinstance(operand, C2PORelease):
                lhs: C2PONode = operand.get_lhs()
                rhs: C2PONode = operand.get_rhs()
                bounds: Interval = operand.interval
                # !(p R q) = !p U !q
                node.replace(C2POUntil(node.ln, C2POLogicalNegate(lhs.ln, lhs), C2POLogicalNegate(rhs.ln, rhs), bounds.lb, bounds.ub))
        elif isinstance(node, C2POLogicalImplies):
            lhs: C2PONode = node.get_lhs()
            rhs: C2PONode = node.get_rhs()
            # p -> q = !p || q
            node.replace(C2POLogicalOr(node.ln, [C2POLogicalNegate(lhs.ln, lhs), rhs]))
        elif isinstance(node, C2POLogicalXor):
            lhs: C2PONode = node.get_lhs()
            rhs: C2PONode = node.get_rhs()
            # p xor q = (p && !q) || (!p && q)
            node.replace(C2POLogicalOr(node.ln, [C2POLogicalAnd(node.ln, [lhs, C2POLogicalNegate(rhs.ln, rhs)]),\
                                       C2POLogicalAnd(node.ln, [C2POLogicalNegate(lhs.ln, lhs), rhs])]))

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_negative_normal_form_util)


def rewrite_set_aggregation(program: C2POProgram):
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
    def rewrite_struct_access_util(node: C2PONode):
        print(f"{node} : {type(node)} : {type(node.get_struct()) if isinstance(node, C2POStructAccess) else ''}")
        if isinstance(node, C2POStructAccess) and not isinstance(node.get_struct(), C2POVariable):
            s: C2POStruct = node.get_struct()
            node.replace(s.get_member(node.member))

    def rewrite_set_aggregation_util(a: C2PONode):
        cur: C2PONode = a

        if isinstance(a, C2POForEach):
            # rewrite_struct_access_util(a.get_set())
            # cur = C2POLogicalAnd(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()])
            # a.replace(cur) 
            # rewrite_struct_access_util(cur)

            postorder(a.get_set(), rewrite_struct_access_util)

            cur = C2POLogicalAnd(a.ln, [rename(a.get_boundvar(), element, a.get_expr()) for element in a.get_set().get_children()])
            print(f"{cur}\n")

            a.replace(cur)

            postorder(cur, rewrite_struct_access_util)
            print(f"{cur}\n---\n")

        elif isinstance(a, C2POForSome):
            rewrite_struct_access_util(a.get_set())
            cur = C2POLogicalOr(a.ln,[rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()])
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, C2POForExactly):
            s: C2POSet = a.get_set()
            rewrite_struct_access_util(a.get_set())
            cur = C2POEqual(a.ln, C2POArithmeticAdd(a.ln, [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.get_num())
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, C2POForAtLeast):
            s: C2POSet = a.get_set()
            rewrite_struct_access_util(s)
            cur = C2POGreaterThanOrEqual(a.ln, C2POArithmeticAdd(a.ln, [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.get_num())
            a.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(a, C2POForAtMost):
            s: C2POSet = a.get_set()
            rewrite_struct_access_util(s)
            cur = C2POLessThanOrEqual(a.ln, C2POArithmeticAdd(a.ln, [rename(a.get_boundvar(),e,a.get_expr()) for e in a.get_set().get_children()]), a.get_num())
            a.replace(cur)
            rewrite_struct_access_util(cur)

        # for c in cur.get_children():
        #     rewrite_set_aggregation_util(c)

    for spec_section in program.get_spec_sections():
        preorder(spec_section, rewrite_set_aggregation_util)


def rewrite_struct_access(program: C2POProgram):
    """
    Rewrites struct access operations to the references member expression.

    Preconditions:
        - program is type correct
        - program has no set aggregation operators

    Postconditions:
        - program has no struct access operations
    """
    def rewrite_struct_access_util(node: C2PONode):
        if isinstance(node, C2POStructAccess):
            s: C2POStruct = node.get_struct()
            node.replace(s.get_member(node.member))

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_struct_access_util)
    program.is_struct_access_free = True


def optimize_rewrite_rules(program: C2POProgram):

    def optimize_rewrite_rules_util(node: C2PONode):
        if isinstance(node, C2POLogicalNegate):
            opnd1 = node.get_operand()
            if isinstance(opnd1, C2POBool):
                if opnd1.value == True:
                    # !true = false
                    node.replace(C2POBool(node.ln, False))
                else:
                    # !false = true
                    node.replace(C2POBool(node.ln, True))
            elif isinstance(opnd1, C2POLogicalNegate):
                # !!p = p
                node.replace(opnd1.get_operand())
            elif isinstance(opnd1, C2POGlobal):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, C2POLogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    node.replace(C2POFuture(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
            elif isinstance(opnd1, C2POFuture):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, C2POLogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    node.replace(C2POGlobal(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub))
        elif isinstance(node, C2POEqual):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(lhs, C2POBool) and isinstance(rhs, C2POBool):
                pass
            elif isinstance(lhs, C2POBool):
                # (true == p) = p
                node.replace(rhs)
            elif isinstance(rhs, C2POBool):
                # (p == true) = p
                node.replace(lhs)
        elif isinstance(node, C2POGlobal):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # G[0,0]p = p
                node.replace(opnd1)
            if isinstance(opnd1, C2POBool):
                if opnd1.value == True:
                    # G[l,u]True = True
                    node.replace(C2POBool(node.ln, True))
                else:
                    # G[l,u]False = False
                    node.replace(C2POBool(node.ln, False))
            elif isinstance(opnd1, C2POGlobal):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                node.replace(C2POGlobal(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, C2POFuture):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    node.replace(C2POFuture(node.ln, opnd2, lb, ub))
        elif isinstance(node, C2POFuture):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # F[0,0]p = p
                node.replace(opnd1)
            if isinstance(opnd1, C2POBool):
                if opnd1.value == True:
                    # F[l,u]True = True
                    node.replace(C2POBool(node.ln, True))
                else:
                    # F[l,u]False = False
                    node.replace(C2POBool(node.ln, False))
            elif isinstance(opnd1, C2POFuture):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                node.replace(C2POFuture(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, C2POGlobal):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    node.replace(C2POGlobal(node.ln, opnd2, lb, ub))
        elif isinstance(node, C2POLogicalAnd):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
            if isinstance(lhs, C2POGlobal) and isinstance(rhs, C2POGlobal):
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
                        node.replace(C2POGlobal(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        node.replace(C2POGlobal(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        node.replace(C2POGlobal(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        node.replace(C2POGlobal(node.ln, p, lb2, max(ub1,ub2)))
                        return

                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                node.replace(C2POGlobal(node.ln, C2POLogicalAnd(node.ln,
                        [C2POGlobal(node.ln, p, lb1-lb3, ub1-ub3), C2POGlobal(node.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
            elif isinstance(lhs, C2POFuture) and isinstance(rhs, C2POFuture):
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
                        node.replace(C2POFuture(node.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        node.replace(C2POFuture(node.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, C2POUntil) and isinstance(rhs, C2POUntil):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    node.replace(C2POUntil(node.ln, C2POLogicalAnd(node.ln, [lhs_lhs, rhs_lhs]), lhs_rhs, lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(node, C2POLogicalOr):
            # Assume binary for now
            lhs = node.get_child(0)
            rhs = node.get_child(1)
            if isinstance(lhs, C2POFuture) and isinstance(rhs, C2POFuture):
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
                        node.replace(C2POFuture(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        node.replace(C2POFuture(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        node.replace(C2POFuture(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        node.replace(C2POFuture(node.ln, p, lb2, max(ub1,ub2)))
                        return

                # TODO: check for when lb==ub==0
                # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                node.replace(C2POFuture(node.ln, C2POLogicalOr(node.ln,
                        [C2POFuture(node.ln, p, lb1-lb3, ub1-ub3), C2POFuture(node.ln, q, lb2-lb3, ub2-ub3)]), lb3, ub3))
            elif isinstance(lhs, C2POGlobal) and isinstance(rhs, C2POGlobal):
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
                        node.replace(C2POGlobal(node.ln, lhs_opnd, lb2, min(ub1,ub2)))
                    elif lb2 >= lb1 and lb2 <= ub1:
                        # l1 <= l2 <= u1
                        node.replace(C2POGlobal(node.ln, lhs_opnd, lb1, min(ub1,ub2)))
            elif isinstance(lhs, C2POUntil) and isinstance(rhs, C2POUntil):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    node.replace(C2POUntil(node.ln, C2POLogicalOr(node.ln, [lhs_rhs, rhs_rhs]), lhs_lhs, lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(node, C2POUntil):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(rhs, C2POGlobal) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                node.replace(C2POGlobal(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))
            elif isinstance(rhs, C2POFuture) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                node.replace(C2POFuture(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))

    for spec_section in program.get_spec_sections():
        postorder(spec_section, optimize_rewrite_rules_util)


# def optimize_stratify_associative_operators(node: C2PONode):
#     """TODO"""

#     def optimize_associative_operators_rec(node: C2PONode):
#         if isinstance(node, C2POLogicalAnd) and len(node.get_children()) > 2:
#             n: int = len(node.get_children())
#             children = [c for c in node.get_children()]
#             wpds = [c.wpd for c in children]
#             wpds.sort(reverse=True)

#             T = max(children, key=lambda c: c.wpd)

#             if (n-2)*(wpds[0]-wpds[1])-wpds[2]+min([c.bpd for c in node.get_children() if c.wpd < wpds[0]]):
#                 node.replace(C2POLogicalAnd(node.ln, [C2POLogicalAnd(node.ln, [c for c in children if c != children[0]]), children[0]]))
#                 children[0].get_parents().remove(node)

#         elif isinstance(node, C2POLogicalOr):
#             max_wpd: int = max([c.wpd for c in node.get_children()])
#             target: C2PONode = next(c for c in node.get_children() if c.wpd == max_wpd)

#             new_children = [c for c in node.get_children() if c != target]
#             new_ast = C2POLogicalOr(node.ln, [C2POLogicalOr(node.ln, new_children), target])

#         for c in node.get_children():
#             optimize_associative_operators_rec(c)

#     optimize_associative_operators_rec(node)