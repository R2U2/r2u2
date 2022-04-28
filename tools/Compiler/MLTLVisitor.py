# Generated from MLTL.g by ANTLR 4.9.3
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


    # Visit a parse tree produced by MLTLParser#contract.
    def visitContract(self, ctx:MLTLParser.ContractContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#PropExpr.
    def visitPropExpr(self, ctx:MLTLParser.PropExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#BoolExpr.
    def visitBoolExpr(self, ctx:MLTLParser.BoolExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#UnaryTemporalExpr.
    def visitUnaryTemporalExpr(self, ctx:MLTLParser.UnaryTemporalExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#ParensExpr.
    def visitParensExpr(self, ctx:MLTLParser.ParensExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#AtomExpr.
    def visitAtomExpr(self, ctx:MLTLParser.AtomExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#BinaryTemporalExpr.
    def visitBinaryTemporalExpr(self, ctx:MLTLParser.BinaryTemporalExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#mapping.
    def visitMapping(self, ctx:MLTLParser.MappingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#setAssignment.
    def visitSetAssignment(self, ctx:MLTLParser.SetAssignmentContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#filterArgument.
    def visitFilterArgument(self, ctx:MLTLParser.FilterArgumentContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#formulaIdentifier.
    def visitFormulaIdentifier(self, ctx:MLTLParser.FormulaIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#setIdentifier.
    def visitSetIdentifier(self, ctx:MLTLParser.SetIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#filterIdentifier.
    def visitFilterIdentifier(self, ctx:MLTLParser.FilterIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#atomicIdentifier.
    def visitAtomicIdentifier(self, ctx:MLTLParser.AtomicIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#signalIdentifier.
    def visitSignalIdentifier(self, ctx:MLTLParser.SignalIdentifierContext):
        return self.visitChildren(ctx)



del MLTLParser