from .ast import *


def optimize_cse(program: C2POProgram) :
    """
    Performs syntactic common sub-expression elimination on program. Uses string representation of each sub-expression to determine syntactic equivalence. Applies CSE to FT/PT formulas separately.

    Preconditions:
        - `program` is type correct.

    Postconditions:
        - Sets of FT/PT specifications have no distinct, syntactically equivalent sub-expressions (i.e., is CSE-reduced).
        - Some nodes in AST may have multiple parents.
    """
    S: Dict[str, C2PONode]

    def optimize_cse_util(node: C2PONode) :
        nonlocal S

        if str(node) in S:
            node.replace(S[str(node)])
        else:
            S[str(node)] = node

    for spec in program.get_spec_sections():
        S = {}
        postorder(spec, optimize_cse_util)

    # TODO: How to do this with potentially many SPEC sections?
    # postorder_iterative(program.get_future_time_spec_sections(), optimize_cse_util)
    # S = {k:v for (k,v) in S.items() if isinstance(v, BZInstruction)}
    # postorder_iterative(program.get_pt_specs(), optimize_cse_util)

    program.is_cse_reduced = True


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


def optimize_stratify_associative_operators(node: C2PONode):
    """TODO"""

    def optimize_associative_operators_rec(node: C2PONode):
        if isinstance(node, C2POLogicalAnd) and len(node.get_children()) > 2:
            n: int = len(node.get_children())
            children = [c for c in node.get_children()]
            wpds = [c.wpd for c in children]
            wpds.sort(reverse=True)

            T = max(children, key=lambda c: c.wpd)

            if (n-2)*(wpds[0]-wpds[1])-wpds[2]+min([c.bpd for c in node.get_children() if c.wpd < wpds[0]]):
                node.replace(C2POLogicalAnd(node.ln, [C2POLogicalAnd(node.ln, [c for c in children if c != children[0]]), children[0]]))
                children[0].get_parents().remove(node)

        elif isinstance(node, C2POLogicalOr):
            max_wpd: int = max([c.wpd for c in node.get_children()])
            target: C2PONode = next(c for c in node.get_children() if c.wpd == max_wpd)

            new_children = [c for c in node.get_children() if c != target]
            new_ast = C2POLogicalOr(node.ln, [C2POLogicalOr(node.ln, new_children), target]) # type: ignore

        for c in node.get_children():
            optimize_associative_operators_rec(c)

    optimize_associative_operators_rec(node)