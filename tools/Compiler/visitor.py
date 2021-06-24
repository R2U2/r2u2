from .MLTLVisitor import MLTLVisitor
from .MLTLParser import MLTLParser
from .AST import *

import re

class Visitor(MLTLVisitor):

    def __init__(self, atomics, signals, labels):
        self.atomics = atomics
        self.signals = signals
        self.labels = labels
        self.contracts = {}
        self.at_instr = {}
        self.status = True


    def visitErrorNode(self, node):
        self.status = False


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
            label = ctx.Identifier()
            if label and not label.getText() in self.labels:
                # preprocessing pass
                self.labels[label.getText()] = ctx.start.line-1
            return STATEMENT(expr, ctx.start.line-1)
        elif ctx.contract():
            self.visit(ctx.contract())
        elif ctx.binding():
            self.visit(ctx.binding())
        elif ctx.mapping():
            self.visit(ctx.mapping())


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
        try:
            if ctx.GLOBALLY():
                expr = self.visit(ctx.expr(0))
                bounds = ctx.Number()
                if len(bounds) == 1:
                    upper = int(bounds[0].getText())
                    return GLOBAL(expr, ub=upper)
                elif len(bounds) == 2:
                    lower = int(bounds[0].getText())
                    upper = int(bounds[1].getText())
                    return GLOBAL(expr, lb=lower, ub=upper)

            elif ctx.FINALLY():
                expr = self.visit(ctx.expr(0))
                bounds = ctx.Number()
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
                bounds = ctx.Number()
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

    # Visit a parse tree produced by MLTLParser#pt_expr.
    def visitPt_expr(self, ctx:MLTLParser.Pt_exprContext):
        try:
            if ctx.YESTERDAY():
                expr = self.visit(ctx.expr(0))
                return YESTERDAY(expr)

            elif ctx.SINCE():
                left = self.visit(ctx.expr(0))
                right = self.visit(ctx.expr(1))
                bounds = ctx.Number()
                if len(bounds) == 1:
                    upper = int(bounds[0].getText())
                    return SINCE(left, right, ub=upper)
                elif len(bounds) == 2:
                    lower = int(bounds[0].getText())
                    upper = int(bounds[1].getText())
                    return SINCE(left, right, lb=lower, ub=upper)

            elif ctx.ONCE():
                expr = self.visit(ctx.expr(0))
                bounds = ctx.Number()
                if len(bounds) == 1:
                    upper = int(bounds[0].getText())
                    return ONCE(expr, ub=upper)
                elif len(bounds) == 2:
                    lower = int(bounds[0].getText())
                    upper = int(bounds[1].getText())
                    return ONCE(expr, lb=lower, ub=upper)

            elif ctx.HISTORICALLY():
                expr = self.visit(ctx.expr(0))
                bounds = ctx.Number()
                if len(bounds) == 0:
                    return HISTORICALLY(expr)
                if len(bounds) == 1:
                    upper = int(bounds[0].getText())
                    return HISTORICALLY(expr, ub=upper)
                elif len(bounds) == 2:
                    lower = int(bounds[0].getText())
                    upper = int(bounds[1].getText())
                    return HISTORICALLY(expr, lb=lower, ub=upper)

        except ValueError:
            print('Error on line ' + str(ctx.start.line) + ': ' + ctx.getText())
            print('Bounds for temporal operators must be positive integers')
            self.status = False

    # Visit a parse tree produced by MLTLParser#parens_expr.
    def visitParens_expr(self, ctx:MLTLParser.Parens_exprContext):
        return self.visit(ctx.expr())

    # Visit a parse tree produced by MLTLParser#bool_expr.
    def visitBool_expr(self, ctx:MLTLParser.Bool_exprContext):
        return BOOL(ctx.getText())

    # Visit a parse tree produced by MLTLParser#atom_expr.
    def visitAtom_expr(self, ctx:MLTLParser.Atom_exprContext):
        identifier = ctx.Identifier().getText()
        if not identifier in self.atomics:
            # preprocessing pass
            self.atomics[identifier] = -2
        #print(ctx.getText())
        return ATOM('a' + str(self.atomics[identifier]))


    # Visit a parse tree produced by MLTLParser#contract.
    def visitContract(self, ctx:MLTLParser.ContractContext):
        label = ctx.Identifier()
        if not label:
            name = ''
        else:
            name = label.getText()
        self.contracts[name] = [ctx.expr(0).getText(), ctx.expr(1).getText()]
        self.visit(ctx.expr(0))
        self.visit(ctx.expr(1))


    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        atom = ctx.Identifier(0).getText()
        filter = ctx.Filter().getText()
        signal = ctx.Identifier(1).getText()
        if len(ctx.Number()) == 2:
            arg = ctx.Number(0).getText()
            comp = ctx.Number(1).getText()
        else:
            arg = '0'
            comp = ctx.Number(0).getText()
        cond = ctx.Conditional().getText()

        if not atom in self.atomics or self.atomics[atom] == -2:
            # preprocessing pass
            self.atomics[atom] = -1

        atom = 'a' + str(self.atomics[atom])

        if not signal in self.signals:
            # preprocessing pass
            self.signals[signal] = -1

        signal = 's' + str(self.signals[signal])

        self.at_instr[atom] = [filter, signal, arg, cond, comp]

        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#mapping.
    def visitMapping(self, ctx:MLTLParser.MappingContext):
        signal = ctx.Identifier().getText()
        index = ctx.Number().getText()
        self.signals[signal] = int(index)
        return self.visitChildren(ctx)
