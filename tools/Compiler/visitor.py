from .MLTLVisitor import MLTLVisitor
from .MLTLParser import MLTLParser
from .AST import *

class Visitor(MLTLVisitor):

    def __init__(self):
        self.ref_atomics = []
        self.mapped_atomics = []
        self.at_instr = {}
        __all__ = ['status','parser']
        self.status = 'pass'


    # Visit a parse tree produced by MLTLParser#program.
    def visitProgram(self, ctx:MLTLParser.ProgramContext):
        prog = PROGRAM()
        statements = ctx.statement()
        for s in statements:
            ret = self.visit(s)
            prog.add(ret)
        return prog


    # Visit a parse tree produced by MLTLParser#statement.
    def visitStatement(self, ctx:MLTLParser.StatementContext):
        if not ctx.expr() is None:
            expr = self.visit(ctx.expr())
            lineno = ctx.start.line
            return STATEMENT(expr, lineno)
        if not ctx.binding() is None:
            binding = self.visit(ctx.binding())


    # Visit a parse tree produced by MLTLParser#prop_expr.
    def visitProp_expr(self, ctx:MLTLParser.Prop_exprContext):
        op = ctx.op.text

        if op == '!':
            val = self.visit(ctx.expr(0))
            return NEG(val)
        elif op == '&':
            left = self.visit(ctx.expr(0))
            right = self.visit(ctx.expr(1))
            return AND(left, right)
        elif op == '|':
            left = self.visit(ctx.expr(0))
            right = self.visit(ctx.expr(1))
            return NEG(AND(NEG(left),NEG(right)))
        elif op == '->':
            left = self.visit(ctx.expr(0))
            right = self.visit(ctx.expr(1))
            return NEG(AND(left,NEG(right)))
        elif op == '<->':
            left = self.visit(ctx.expr(0))
            right = self.visit(ctx.expr(1))
            return AND(NEG(AND(left,NEG(right))),NEG(AND(right,NEG(left))))


    # Visit a parse tree produced by MLTLParser#ft_expr.
    def visitFt_expr(self, ctx:MLTLParser.Ft_exprContext):
        if ctx.GLOBALLY():
            expr = self.visit(ctx.expr(0))
            bounds = ctx.Natural()
            if len(bounds) == 1:
                upper = int(bounds[0].getText())
                return GLOBAL(expr, ub=upper)
            elif len(bounds) == 2:
                lower = int(bounds[0].getText())
                upper = int(bounds[1].getText())
                return GLOBAL(expr, lb=lower, ub=upper)

        elif ctx.FINALLY():
            expr = self.visit(ctx.expr(0))
            bounds = ctx.Natural()
            if len(bounds) == 1:
                upper = int(bounds[0].getText())
                return UNTIL(BOOL('TRUE'), expr, ub=upper)
            elif len(bounds) == 2:
                lower = int(bounds[0].getText())
                upper = int(bounds[1].getText())
                return UNTIL(BOOL('TRUE'), expr, lb=lower, ub=upper)

        elif ctx.UNTIL():
            left = self.visit(ctx.expr(0))
            right = self.visit(ctx.expr(1))
            bounds = ctx.Natural()
            if len(bounds) == 1:
                upper = int(bounds[0].getText())
                return UNTIL(left, right, ub=upper)
            elif len(bounds) == 2:
                lower = int(bounds[0].getText())
                upper = int(bounds[1].getText())
                return UNTIL(left, right, lb=lower, ub=upper)

        elif ctx.RELEASE():
            left = self.visit(ctx.expr(0))
            right = self.visit(ctx.expr(1))
            bounds = ctx.Natural()
            if len(bounds) == 1:
                upper = int(ctx.Natural(0).getText())
                return RELEASE(left, right, ub=upper)
            elif len(bounds) == 2:
                lower = int(bounds[0].getText())
                upper = int(bounds[1].getText())
                return RELEASE(left, right, lb=lower, ub=upper)

    # Visit a parse tree produced by MLTLParser#pt_expr.
    def visitPt_expr(self, ctx:MLTLParser.Pt_exprContext):
        if ctx.YESTERDAY():
            expr = self.visit(ctx.expr(0))
            return YESTERDAY(expr)

        elif ctx.SINCE():
            left = self.visit(ctx.expr(0))
            right = self.visit(ctx.expr(1))
            bounds = ctx.Natural()
            if len(bounds) == 1:
                upper = int(bounds[0].getText())
                return SINCE(left, right, ub=upper)
            elif len(bounds) == 2:
                lower = int(bounds[0].getText())
                upper = int(bounds[1].getText())
                return SINCE(left, right, lb=lower, ub=upper)

        elif ctx.ONCE():
            expr = self.visit(ctx.expr(0))
            bounds = ctx.Natural()
            if len(bounds) == 1:
                upper = int(bounds[0].getText())
                return ONCE(expr, ub=upper)
            elif len(bounds) == 2:
                lower = int(bounds[0].getText())
                upper = int(bounds[1].getText())
                return ONCE(expr, lb=lower, ub=upper)

        elif ctx.HISTORICALLY():
            expr = self.visit(ctx.expr(0))
            bounds = ctx.Natural()
            if len(bounds) == 0:
                return HISTORICALLY(expr)
            if len(bounds) == 1:
                upper = int(bounds[0].getText())
                return HISTORICALLY(expr, ub=upper)
            elif len(bounds) == 2:
                lower = int(bounds[0].getText())
                upper = int(bounds[1].getText())
                return HISTORICALLY(expr, lb=lower, ub=upper)

    # Visit a parse tree produced by MLTLParser#parens_expr.
    def visitParens_expr(self, ctx:MLTLParser.Parens_exprContext):
        return self.visit(ctx.expr())

    # Visit a parse tree produced by MLTLParser#bool_expr.
    def visitBool_expr(self, ctx:MLTLParser.Bool_exprContext):
        return BOOL(ctx.getText())

    # Visit a parse tree produced by MLTLParser#atom_expr.
    def visitAtom_expr(self, ctx:MLTLParser.Atom_exprContext):
        identifier = str(ctx.Identifier())
        if identifier not in self.ref_atomics:
            self.ref_atomics.append(identifier)
        return ATOM(str(ctx.Identifier()))

    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        atom = ctx.Identifier(0).getText()
        filter = ctx.Filter().getText()
        signal = ctx.Identifier(1).getText()
        if not ctx.Natural() is None:
            arg = ctx.Natural().getText()
        else:
            arg = '0'
        cond = ctx.Conditional().getText()
        comp = ctx.Number().getText()

        self.at_instr[atom] = [filter, signal, arg, cond, comp]

        self.mapped_atomics.append(atom)

        return self.visitChildren(ctx)
