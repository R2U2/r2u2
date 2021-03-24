# Generated from MLTL.g by ANTLR 4.9.2
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .MLTLParser import MLTLParser
else:
    from MLTLParser import MLTLParser

# This class defines a complete generic visitor for a parse tree produced by MLTLParser.

class MLTLVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by MLTLParser#program.
    def visitProgram(self, ctx:MLTLParser.ProgramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#statement.
    def visitStatement(self, ctx:MLTLParser.StatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#prop_expr.
    def visitProp_expr(self, ctx:MLTLParser.Prop_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#bool_expr.
    def visitBool_expr(self, ctx:MLTLParser.Bool_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#pt_expr.
    def visitPt_expr(self, ctx:MLTLParser.Pt_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#atom_expr.
    def visitAtom_expr(self, ctx:MLTLParser.Atom_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#parens_expr.
    def visitParens_expr(self, ctx:MLTLParser.Parens_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#ft_expr.
    def visitFt_expr(self, ctx:MLTLParser.Ft_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        return self.visitChildren(ctx)



del MLTLParser