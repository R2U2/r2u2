from .MLTLVisitor import MLTLVisitor
from .MLTLParser import MLTLParser
from .AST import *

class FTVisitor(MLTLVisitor):

    def __init__(self, atomics):
        self.atomics = atomics

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
        if ctx.expr():
            expr = self.visit(ctx.expr())
            return STATEMENT(expr, ctx.start.line-1)
        else:
            print('ERROR: parsing error for satement '+ctx.getText())


    # Visit a parse tree produced by MLTLParser#PropExpr.
    def visitPropExpr(self, ctx:MLTLParser.PropExprContext):
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


    # Visit a parse tree produced by MLTLParser#UnaryTemporalExpr.
    def visitUnaryTemporalExpr(self, ctx:MLTLParser.UnaryTemporalExprContext):
        op = ctx.UnaryTemporalOp().getText()
        try:
            if op == 'G':
                expr = self.visit(ctx.expr())
                bounds = ctx.Number()
                if len(bounds) == 1:
                    upper = int(bounds[0].getText())
                    return GLOBAL(expr, ub=upper)
                elif len(bounds) == 2:
                    lower = int(bounds[0].getText())
                    upper = int(bounds[1].getText())
                    return GLOBAL(expr, lb=lower, ub=upper)
            elif op == 'F':
                expr = self.visit(ctx.expr())
                bounds = ctx.Number()
                if len(bounds) == 1:
                    upper = int(bounds[0].getText())
                    return UNTIL(BOOL('TRUE'), expr, ub=upper)
                elif len(bounds) == 2:
                    lower = int(bounds[0].getText())
                    upper = int(bounds[1].getText())
                    return UNTIL(BOOL('TRUE'), expr, lb=lower, ub=upper)
        except ValueError:
            print('Error on line ' + str(ctx.start.line) + ': ' + ctx.getText())
            print('Bounds for temporal operators must be integers')
            self.status = False


    # Visit a parse tree produced by MLTLParser#BinaryTemporalExpr.
    def visitBinaryTemporalExpr(self, ctx:MLTLParser.BinaryTemporalExprContext):
        op = ctx.BinaryTemporalOp().getText()
        try:
            if op == 'U':
                    left = self.visit(ctx.expr(0))
                    right = self.visit(ctx.expr(1))
                    bounds = ctx.Number()
                    if len(bounds) == 1:
                        upper = int(bounds[0].getText())
                        return UNTIL(left, right, ub=upper)
                    elif len(bounds) == 2:
                        lower = int(bounds[0].getText())
                        upper = int(bounds[1].getText())
                        return UNTIL(left, right, lb=lower, ub=upper)
            elif op == 'R':
                left = self.visit(ctx.expr(0))
                right = self.visit(ctx.expr(1))
                bounds = ctx.Number()
                if len(bounds) == 1:
                    upper = int(ctx.Number(0).getText())
                    return NEG(UNTIL(NEG(left),NEG(right),ub=upper))
                elif len(bounds) == 2:
                    lower = int(bounds[0].getText())
                    upper = int(bounds[1].getText())
                    return NEG(UNTIL(NEG(left),NEG(right),lb=lower,ub=upper))
        except ValueError:
            print('Error on line ' + str(ctx.start.line) + ': ' + ctx.getText())
            print('Bounds for temporal operators must be integers')
            self.status = False


    # Visit a parse tree produced by MLTLParser#ParensExpr.
    def visitParensExpr(self, ctx:MLTLParser.ParensExprContext):
        return self.visit(ctx.expr())


    # Visit a parse tree produced by MLTLParser#BoolExpr.   
    def visitBoolExpr(self, ctx:MLTLParser.BoolExprContext):
        return BOOL(ctx.getText())


    # Visit a parse tree produced by MLTLParser#AtomExpr.
    def visitAtomExpr(self, ctx:MLTLParser.AtomExprContext):
        identifier = ctx.atomicIdentifier().getText()
        return ATOM('a' + str(self.atomics[identifier]))

    
    # Visit a parse tree produced by MLTLParser#formulaIdentifier.
    def visitFormulaIdentifier(self, ctx:MLTLParser.FormulaIdentifierContext):
        return self.visitChildren(ctx)



del MLTLParser