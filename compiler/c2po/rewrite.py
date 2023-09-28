from .ast import *


def rewrite_definitions(program: C2POProgram, context: C2POContext):
    
    def rewrite_definitions_util(node: C2PONode):
        if isinstance(node, C2POVariable):
            if node.symbol in context.definitions:
                node.replace(context.definitions[node.symbol])
            elif node.symbol in context.specifications:
                node.replace(context.specifications[node.symbol].get_expr())

    for definition in context.definitions.values():
        postorder(definition, rewrite_definitions_util)

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_definitions_util)


def rewrite_function_calls(program: C2POProgram, context: C2POContext):

    def rewrite_function_calls_util(node: C2PONode):
        if isinstance(node, C2POFunctionCall) and node.symbol in context.structs:
            struct_members = [m for m in context.structs[node.symbol].keys()]
            node.replace(
                C2POStruct(
                    node.ln, 
                    node.symbol, 
                    {name:struct_members.index(name) for name in context.structs[node.symbol].keys()}, 
                    cast(List[C2PONode], reversed(node.get_children()))
                )
            )

    for definition in context.definitions.values():
        postorder(definition, rewrite_function_calls_util)

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_function_calls_util)


def rewrite_contracts(program: C2POProgram, context: C2POContext):
    """Removes each contract from each specification in Program and adds the corresponding conditions to track."""

    for spec_section in program.get_spec_sections():
        for contract in [c for c in spec_section.get_children() if isinstance(c, C2POContract)]:
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


def rewrite_set_aggregation(program: C2POProgram):
    """
    Rewrites set aggregation operators into corresponding BZ and TL operations e.g., foreach is rewritten into a conjunction.

    Preconditions:
        - program is type correct

    Postconditions:
        - program has no struct access operations
        - program has no variables
    """

    def rewrite_struct_access_util(node: C2PONode):
        if isinstance(node, C2POStructAccess) and not isinstance(node.get_struct(), C2POVariable):
            s: C2POStruct = node.get_struct()
            node.replace(s.get_member(node.member))

    def rewrite_set_aggregation_util(node: C2PONode):
        cur: C2PONode = node

        if isinstance(node, C2POForEach):
            postorder(node.get_set(), rewrite_struct_access_util)

            cur = C2POLogicalAnd(node.ln, [rename(node.get_boundvar(), element, node.get_expr()) for element in node.get_set().get_children()])

            node.replace(cur)
        elif isinstance(node, C2POForSome):
            rewrite_struct_access_util(node.get_set())
            cur = C2POLogicalOr(node.ln,[rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().get_children()])
            node.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(node, C2POForExactly):
            s: C2POSet = node.get_set()
            rewrite_struct_access_util(node.get_set())
            cur = C2POEqual(node.ln, C2POArithmeticAdd(node.ln, [rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().get_children()]), node.get_num())
            node.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(node, C2POForAtLeast):
            s: C2POSet = node.get_set()
            rewrite_struct_access_util(s)
            cur = C2POGreaterThanOrEqual(node.ln, C2POArithmeticAdd(node.ln, [rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().get_children()]), node.get_num())
            node.replace(cur)
            rewrite_struct_access_util(cur)
        elif isinstance(node, C2POForAtMost):
            s: C2POSet = node.get_set()
            rewrite_struct_access_util(s)
            cur = C2POLessThanOrEqual(node.ln, C2POArithmeticAdd(node.ln, [rename(node.get_boundvar(),e,node.get_expr()) for e in node.get_set().get_children()]), node.get_num())
            node.replace(cur)
            rewrite_struct_access_util(cur)

        for c in cur.get_children():
            rewrite_set_aggregation_util(c)

    for spec_section in program.get_spec_sections():
        rewrite_set_aggregation_util(spec_section)


def rewrite_extended_operators(program: C2POProgram):
    """
    Rewrites program formulas without extended operators i.e., formulas with only negation, conjunction, until, global, and future.

    Preconditions:
        - program is type correct.

    Postconditions:
        - program formulas only have negation, conjunction, until, and global TL operators.
    """

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


def rewrite_struct_accesses(program: C2POProgram):
    """
    Rewrites struct access operations to the references member expression.

    Preconditions:
        - program is type correct
        - program has no set aggregation operators

    Postconditions:
        - program has no struct access operations
    """
    def rewrite_struct_accesses_util(node: C2PONode):
        if isinstance(node, C2POStructAccess):
            s: C2POStruct = node.get_struct()
            node.replace(s.get_member(node.member))

    for spec_section in program.get_spec_sections():
        postorder(spec_section, rewrite_struct_accesses_util)
    program.is_struct_access_free = True


