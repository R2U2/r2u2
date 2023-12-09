from c2po.ast import *
from c2po.egraph import *

def transform_definitions(program: C2POProgram, context: C2POContext):
    """Transforms each definition symbol in the definitions and specifications of `program` to its expanded definition. This is essentially macro expansion."""
    
    def _transform_definitions(node: C2PONode):
        if isinstance(node, C2POVariable):
            if node.symbol in context.definitions:
                node.replace(context.definitions[node.symbol])
            elif node.symbol in context.specifications:
                node.replace(context.specifications[node.symbol].get_expr())

    for node in [n for d in context.definitions.values() for n in postorder(d)]:
        _transform_definitions(node)

    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _transform_definitions(node)


def transform_function_calls(program: C2POProgram, context: C2POContext):
    """Transforms each function call in `program` that corresponds to a struct instantiation to a `C2POStruct`."""

    def _transform_function_calls(node: C2PONode):
        if isinstance(node, C2POFunctionCall) and node.symbol in context.structs:
            struct_members = [m for m in context.structs[node.symbol].keys()]
            node.replace(
                C2POStruct(
                    node.ln, 
                    node.symbol, 
                    {name:struct_members.index(name) for name in context.structs[node.symbol].keys()}, 
                    cast(List[C2PONode], node.children)
                )
            )

    for node in [n for d in context.definitions.values() for n in postorder(d)]:
        _transform_function_calls(node)

    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _transform_function_calls(node)


def transform_contracts(program: C2POProgram, context: C2POContext):
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""

    for spec_section in program.get_spec_sections():
        for contract in [c for c in spec_section.children if isinstance(c, C2POContract)]:
            spec_section.remove_child(contract)

            spec_section.add_child(C2POSpecification(
                contract.ln,
                contract.symbol,
                contract.formula_numbers[0],
                contract.get_assumption()
            ))

            spec_section.add_child(C2POSpecification(
                contract.ln,
                contract.symbol,
                contract.formula_numbers[1],
                C2POLogicalImplies(contract.ln, contract.get_assumption(), contract.get_guarantee())
            ))

            spec_section.add_child(C2POSpecification(
                contract.ln,
                contract.symbol,
                contract.formula_numbers[2],
                C2POLogicalAnd(contract.ln, [contract.get_assumption(), contract.get_guarantee()])
            ))


def transform_set_aggregation(program: C2POProgram, context: C2POContext):
    """Transforms set aggregation operators into equivalent engine-supported operations e.g., `foreach` is rewritten into a conjunction."""

    def _transform_struct_access(node: C2PONode):
        if isinstance(node, C2POStructAccess) and not isinstance(node.get_struct(), C2POVariable):
            s: C2POStruct = node.get_struct()
            member = s.get_member(node.member)
            if member:
                node.replace(member)

    def _transform_set_aggregation(node: C2PONode):
        cur: C2PONode = node

        if isinstance(node, C2POForEach):
            for _node in postorder(node.get_set()):
                _transform_struct_access(_node)

            cur = C2POLogicalAnd(node.ln, [rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().children])

            node.replace(cur)
        elif isinstance(node, C2POForSome):
            _transform_struct_access(node.get_set())
            cur = C2POLogicalOr(node.ln,[rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().children])
            node.replace(cur)
            _transform_struct_access(cur)
        elif isinstance(node, C2POForExactly):
            s: C2POSet = node.get_set()
            _transform_struct_access(node.get_set())
            cur = C2POEqual(node.ln, C2POArithmeticAdd(node.ln, [rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().children]), node.get_num())
            node.replace(cur)
            _transform_struct_access(cur)
        elif isinstance(node, C2POForAtLeast):
            s: C2POSet = node.get_set()
            _transform_struct_access(s)
            cur = C2POGreaterThanOrEqual(node.ln, C2POArithmeticAdd(node.ln, [rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().children]), node.get_num())
            node.replace(cur)
            _transform_struct_access(cur)
        elif isinstance(node, C2POForAtMost):
            s: C2POSet = node.get_set()
            _transform_struct_access(s)
            cur = C2POLessThanOrEqual(node.ln, C2POArithmeticAdd(node.ln, [rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().children]), node.get_num())
            node.replace(cur)
            _transform_struct_access(cur)

        for c in cur.children:
            _transform_set_aggregation(c)

    for spec_section in program.get_spec_sections():
        _transform_set_aggregation(spec_section)


def transform_struct_accesses(program: C2POProgram, context: C2POContext):
    """Transforms struct access operations to the underlying member expression."""
    def _transform_struct_accesses(node: C2PONode):
        if isinstance(node, C2POStructAccess):
            s: C2POStruct = node.get_struct()
            member = s.get_member(node.member)
            if member:
                node.replace(member)

    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _transform_struct_accesses(node)
        

def transform_extended_operators(program: C2POProgram, context: C2POContext):
    """Transforms specifications in `program` to remove extended operators (or, xor, implies, iff, release, future)."""
    def _transform_extended_operators(node: C2PONode):
        if isinstance(node, C2POLogicalOperator):
            if isinstance(node, C2POLogicalOr):
                # p || q = !(!p && !q)
                node.replace(C2POLogicalNegate(node.ln, C2POLogicalAnd(node.ln, [C2POLogicalNegate(c.ln, c) for c in node.children])))
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
            
    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _transform_extended_operators(node)


def transform_boolean_normal_form(program: C2POProgram, context: C2POContext):
    """Converts program formulas to Boolean Normal Form (BNF). An MLTL formula in BNF has only negation, conjunction, and until operators."""
    def _transform_boolean_normal_form(node: C2PONode):

        if isinstance(node, C2POLogicalOr):
            # p || q = !(!p && !q)
            node.replace(C2POLogicalNegate(node.ln, C2POLogicalAnd(node.ln, [C2POLogicalNegate(c.ln, c) for c in node.children])))
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
            
    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _transform_boolean_normal_form(node)


def transform_negative_normal_form(program: C2POProgram, context: C2POContext):
    """Converts program to Negative Normal Form (NNF). An MLTL formula in NNF has all MLTL operators, but negations are only applied to literals."""
    def _transform_negative_normal_form(node: C2PONode):
        if isinstance(node, C2POLogicalNegate):
            operand = node.get_operand()
            if isinstance(operand, C2POLogicalNegate):
                # !!p = p
                node.replace(operand.get_operand())
            if isinstance(operand, C2POLogicalOr):
                # !(p || q) = !p && !q
                node.replace(C2POLogicalAnd(node.ln, [C2POLogicalNegate(c.ln, c) for c in operand.children]))
            if isinstance(operand, C2POLogicalAnd):
                # !(p && q) = !p || !q
                node.replace(C2POLogicalOr(node.ln, [C2POLogicalNegate(c.ln, c) for c in operand.children]))
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
            
    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _transform_negative_normal_form(node)


def optimize_rewrite_rules(program: C2POProgram, context: C2POContext):
    """Applies MLTL rewrite rules to reduce required SCQ memory."""
    def _optimize_rewrite_rules(node: C2PONode):
        new: Optional[C2PONode] = None

        if isinstance(node, C2POLogicalNegate):
            opnd1 = node.get_operand()
            if isinstance(opnd1, C2POBool):
                if opnd1.value == True:
                    # !true = false
                    new = C2POBool(node.ln, False)
                else:
                    # !false = true
                    new = C2POBool(node.ln, True)
            elif isinstance(opnd1, C2POLogicalNegate):
                # !!p = p
                new = opnd1.get_operand()
            elif isinstance(opnd1, C2POGlobal):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, C2POLogicalNegate):
                    # !(G[l,u](!p)) = F[l,u]p
                    new = C2POFuture(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub)
            elif isinstance(opnd1, C2POFuture):
                opnd2 = opnd1.get_operand()
                if isinstance(opnd2, C2POLogicalNegate):
                    # !(F[l,u](!p)) = G[l,u]p
                    new = C2POGlobal(node.ln, opnd2.get_operand(), opnd1.interval.lb, opnd1.interval.ub)
        elif isinstance(node, C2POEqual):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(lhs, C2POBool) and isinstance(rhs, C2POBool):
                pass
            elif isinstance(lhs, C2POBool):
                # (true == p) = p
                new = (rhs)
            elif isinstance(rhs, C2POBool):
                # (p == true) = p
                new = (lhs)
        elif isinstance(node, C2POGlobal):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # G[0,0]p = p
                new = (opnd1)
            if isinstance(opnd1, C2POBool):
                if opnd1.value == True:
                    # G[l,u]True = True
                    new = (C2POBool(node.ln, True))
                else:
                    # G[l,u]False = False
                    new = (C2POBool(node.ln, False))
            elif isinstance(opnd1, C2POGlobal):
                # G[l1,u1](G[l2,u2]p) = G[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                new = (C2POGlobal(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, C2POFuture):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # G[a,a](F[l,u]p) = F[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    new = (C2POFuture(node.ln, opnd2, lb, ub))
        elif isinstance(node, C2POFuture):
            opnd1 = node.get_operand()
            if node.interval.lb == 0 and node.interval.ub == 0:
                # F[0,0]p = p
                new = (opnd1)
            if isinstance(opnd1, C2POBool):
                if opnd1.value == True:
                    # F[l,u]True = True
                    new = (C2POBool(node.ln, True))
                else:
                    # F[l,u]False = False
                    new = (C2POBool(node.ln, False))
            elif isinstance(opnd1, C2POFuture):
                # F[l1,u1](F[l2,u2]p) = F[l1+l2,u1+u2]p
                opnd2 = opnd1.get_operand()
                lb: int = node.interval.lb + opnd1.interval.lb
                ub: int = node.interval.ub + opnd1.interval.ub
                new = (C2POFuture(node.ln, opnd2, lb, ub))
            elif isinstance(opnd1, C2POGlobal):
                opnd2 = opnd1.get_operand()
                if node.interval.lb == node.interval.ub:
                    # F[a,a](G[l,u]p) = G[l+a,u+a]p
                    lb: int = node.interval.lb + opnd1.interval.lb
                    ub: int = node.interval.ub + opnd1.interval.ub
                    new = (C2POGlobal(node.ln, opnd2, lb, ub))
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
                        new = (C2POGlobal(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = (C2POGlobal(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        new = (C2POGlobal(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        new = (C2POGlobal(node.ln, p, lb2, max(ub1,ub2)))
                        return

                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                new = (C2POGlobal(node.ln, C2POLogicalAnd(node.ln,
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
                    if lb1 >= lb2 and ub1 <= ub2:
                        # l2 <= l1 <= u1 <= u2
                        new = (C2POFuture(node.ln, lhs_opnd, lb1, ub1))
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = (C2POFuture(node.ln, lhs_opnd, lb2, ub2))
            elif isinstance(lhs, C2POUntil) and isinstance(rhs, C2POUntil):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                # check for syntactic equivalence
                if str(lhs_rhs) == str(rhs_rhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (r U[l,u2] q) = (p && r) U[l,min(u1,u2)] q
                    new = (C2POUntil(node.ln, C2POLogicalAnd(node.ln, [lhs_lhs, rhs_lhs]), lhs_rhs, lhs.interval.lb,
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
                        new = (C2POFuture(node.ln, p, lb1, ub1))
                        return
                    elif lb2 <= lb1 and ub2 >= ub1:
                        # lb2 <= lb1 <= ub1 <= ub2
                        new = (C2POFuture(node.ln, p, lb2, ub2))
                        return
                    elif lb1 <= lb2 and lb2 <= ub1+1:
                        # lb1 <= lb2 <= ub1+1
                        new = (C2POFuture(node.ln, p, lb1, max(ub1,ub2)))
                        return
                    elif lb2 <= lb1 and lb1 <= ub2+1:
                        # lb2 <= lb1 <= ub2+1
                        new = (C2POFuture(node.ln, p, lb2, max(ub1,ub2)))
                        return

                # TODO: check for when lb==ub==0
                # (F[l1,u1]p) || (F[l2,u2]q) = F[l3,u3](F[l1-l3,u1-u3]p || F[l2-l3,u2-u3]q)
                lb3: int = min(lb1, lb2)
                ub3: int = lb3 + min(ub1-lb1,ub2-lb2)

                new = (C2POFuture(node.ln, C2POLogicalOr(node.ln,
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
                    if lb1 >= lb2 and ub1 <= ub2:
                        # l2 <= l1 <= u1 <= u2
                        new = (C2POGlobal(node.ln, lhs_opnd, lb1, ub1))
                    elif lb2 >= lb1 and ub2 <= ub1:
                        # l1 <= l2 <= u1
                        new = (C2POGlobal(node.ln, lhs_opnd, lb2, ub2))
            elif isinstance(lhs, C2POUntil) and isinstance(rhs, C2POUntil):
                lhs_lhs = lhs.get_lhs()
                lhs_rhs = lhs.get_rhs()
                rhs_lhs = rhs.get_lhs()
                rhs_rhs = rhs.get_rhs()
                if str(lhs_lhs) == str(rhs_lhs) and lhs.interval.lb == rhs.interval.lb:
                    # (p U[l,u1] q) && (p U[l,u2] r) = p U[l,min(u1,u2)] (q || r)
                    new = (C2POUntil(node.ln, C2POLogicalOr(node.ln, [lhs_rhs, rhs_rhs]), lhs_lhs, lhs.interval.lb,
                        min(lhs.interval.ub, rhs.interval.ub)))
        elif isinstance(node, C2POUntil):
            lhs = node.get_lhs()
            rhs = node.get_rhs()
            if isinstance(rhs, C2POGlobal) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (G[0,u2]p) = G[l,l+u2]p
                new = (C2POGlobal(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))
            elif isinstance(rhs, C2POFuture) and rhs.interval.lb == 0 and str(lhs) == str(rhs.get_operand()):
                # p U[l,u1] (F[0,u2]p) = F[l,l+u2]p
                new = (C2POFuture(node.ln, lhs, node.interval.lb, node.interval.lb+rhs.interval.ub))

        if new:
            logger.debug(f"REWRITE:\n\t{node}\n\t\t===>\n\t{new}")
            node.replace(new)

    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _optimize_rewrite_rules(node)


def optimize_cse(program: C2POProgram, context: C2POContext) :
    """Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence. Applies CSE to FT/PT formulas separately."""
    S: Dict[str, C2PONode]

    logger.debug(f"CSE: Beginning CSE")

    def _optimize_cse(node: C2PONode) :
        nonlocal S

        if str(node) in S:
            logger.debug(f"CSE: Replacing --- {node}")
            node.replace(S[str(node)])
        else:
            logger.debug(f"CSE: Visiting ---- {node}")
            S[str(node)] = node

    for spec_section in program.get_spec_sections():
        S = {}
        for node in postorder(spec_section):
            _optimize_cse(node)

    program.is_cse_reduced = True


def compute_atomics(program: C2POProgram, context: C2POContext):
    """Compute atomics and store them in `context`. An atomic is any expression that is *not* computed by the TL engine, but has at least one parent that is computed by the TL engine."""
    id: int = 0
    
    def _compute_atomics(node: C2PONode):
        nonlocal id

        if not isinstance(node, C2POExpression):
            return

        if node.engine == R2U2Engine.TEMPORAL_LOGIC:
            return

        if isinstance(node, C2POBool):
            return

        for parent in [p for p in node.parents if isinstance(p, C2POExpression)]:
            if parent.engine == R2U2Engine.TEMPORAL_LOGIC:
                context.atomics.add(node)
                if node.atomic_id < 0:
                    node.atomic_id = id
                    id += 1

    for node in [n for s in program.get_specs() for n in postorder(s)]:
        _compute_atomics(node)

    logger.debug(f"ATM: Computed atomics:\n\t[{', '.join(f'({a},{a.atomic_id})' for a in context.atomics)}]")


def compute_scq_sizes(program: C2POProgram, context: C2POContext):
    """Computes SCQ sizes for each node."""
    spec_section_total_scq_size = 0

    def _compute_scq_size(expr: C2PONode):
        nonlocal spec_section_total_scq_size
        
        if not isinstance(expr, C2POExpression):
            return

        if isinstance(expr, C2POSpecSection):
            expr.total_scq_size = spec_section_total_scq_size
            spec_section_total_scq_size = 0
            return
            
        if isinstance(expr, C2POSpecification):
            expr.scq_size = 1
            expr.total_scq_size = expr.get_expr().total_scq_size + expr.scq_size
            spec_section_total_scq_size += expr.scq_size
            expr.scq = (spec_section_total_scq_size - expr.scq_size, spec_section_total_scq_size)
            return

        if expr.engine != R2U2Engine.TEMPORAL_LOGIC and expr not in context.atomics:
            return

        max_wpd = max([sibling.wpd for sibling in expr.get_siblings()] + [0])

        # need the +3 b/c of implementation -- ask Brian
        expr.scq_size = max(max_wpd - expr.bpd, 0) + 3
        expr.total_scq_size = sum([c.total_scq_size for c in expr.get_children() if c.scq_size > -1]) + expr.scq_size
        spec_section_total_scq_size += expr.scq_size

        expr.scq = (spec_section_total_scq_size - expr.scq_size, spec_section_total_scq_size)

    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        _compute_scq_size(node)


def optimize_egraph(program: C2POProgram, context: C2POContext):

    def match(egraph: EGraph) -> List[Tuple[C2POExpression, int]]:
        for enode in egraph.enodes():
            pass

        return []

    egraph = EGraph(set(program.get_top_level_expressions()))
    
    # matches = match(egraph)
    # while len(matches) != 0:
    #     for (repl, eclass1) in matches:
    #         eclass2 = egraph.add(repl)
    #         egraph.merge(eclass1, eclass2)

    #     egraph.rebuild()

    for node in [n for s in program.get_spec_sections() for n in postorder(s)]:
        if isinstance(node, C2POLogicalAnd):
            new_children = []
            for child in [c for c in node.children]:
                if isinstance(child, C2POLogicalAnd):
                    new_children += child.children
                else:
                    new_children.append(child)

            print("----------------")
            print("Pre")
            print(egraph)

            eclass_id = egraph.add(C2POLogicalAnd(node.ln, new_children))
            egraph.merge(egraph.eclass[egraph.canonicalize(node)], eclass_id)
            egraph.rebuild()

            print("----------------")
            print("Post")
            print(egraph)

    # print(egraph)


# A C2POTransform is a function with the signature:
#    transform(program, context) -> None
C2POTransform = Callable[[C2POProgram, C2POContext], None]

# Note: this is ORDER-SENSITIVE
TRANSFORM_PIPELINE: List[C2POTransform] = [
    transform_definitions,
    transform_function_calls,
    transform_contracts,
    transform_set_aggregation,
    transform_struct_accesses,
    optimize_rewrite_rules,
    optimize_egraph,
    transform_extended_operators,
    transform_negative_normal_form,
    transform_boolean_normal_form,
    optimize_cse,
    compute_atomics, # not a transform, but needed for assembly+analysis
    compute_scq_sizes, # not a transform, but needed for assembly+analysis
]
