from .MLTLVisitor import MLTLVisitor
from .MLTLParser import MLTLParser
from .AST import *

import re # I hate to do this...

class PreprocessVisitor(MLTLVisitor):
    """
    This visitor has these responsibilites:
        * collect and resolve atomic aliases
        * collect and resolve signal aliases
        * resolve contracts
        * check for mixed-time formulas
    """

    def __init__(self):
        self.atomics = {}
        self.ref_atomics = []
        self.bound_atomics = []
        self.supp_bindings = []
        self.ref_signals = []
        self.mapped_signals = []
        self.supp_mappings = []
        self.formula_labels = []
        self.num_ft = 0
        self.num_pt = 0
        self.in_ft = False # track if expr is nested in FT operator
        self.in_pt = False # track if expr is nested in PT operator
        self.status = True


    def visitErrorNode(self, node):
        self.status = False


    # Visit a parse tree produced by MLTLParser#program.
    def visitProgram(self, ctx:MLTLParser.ProgramContext):
        ret = self.visitChildren(ctx)

        # resolve atomics -- any referenced, unbound atomic must be bound to some
        # default boolean value
        for atomic in (set(self.ref_atomics).difference(set(self.bound_atomics))):
            print(atomic)
            if(re.match('a\d+',atomic)):
                idx = re.search('\d+',atomic).group()
                self.supp_bindings.append('a'+idx+' := bool(s'+idx+') == 1;')
            else:
                print('WARNING: atomic referenced but not bound: ' + atomic)

        # resolve signals

        return ret


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
        if ctx.UnaryTemporalOp().getText() == 'G' or ctx.UnaryTemporalOp().getText() == 'F':
            # track number of PT/FT formulas
            if not self.in_ft and not self.in_pt:
                self.num_ft += 1

            if self.in_pt:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.in_ft = True
            ret = self.visitChildren(ctx)
            self.in_ft = False
        else: # unary operator is PT (H or O)
            # track number of PT/FT formulas
            if not self.in_ft and not self.in_pt:
                self.num_pt += 1

            if self.in_ft:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.in_pt = True
            ret = self.visitChildren(ctx)
            self.in_pt = False


    # Visit a parse tree produced by MLTLParser#BinaryTemporalExpr.
    def visitBinaryTemporalExpr(self, ctx:MLTLParser.BinaryTemporalExprContext):
        if ctx.BinaryTemporalOp().getText() == 'U' or ctx.BinaryTemporalOp().getText() == 'R':
            # track number of PT/FT formulas
            if not self.in_ft and not self.in_pt:
                self.num_ft += 1

            if self.in_pt:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.in_ft = True
            ret = self.visitChildren(ctx)
            self.in_ft = False
        else: # binary operator is PT (Y or S)
            # track number of PT/FT formulas
            if not self.in_ft and not self.in_pt:
                self.num_pt += 1

            if self.in_ft:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.in_pt = True
            ret = self.visitChildren(ctx)
            self.in_pt = False


    # Visit a parse tree produced by MLTLParser#ParensExpr.
    def visitParensExpr(self, ctx:MLTLParser.ParensExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#AtomExpr.
    def visitAtomExpr(self, ctx:MLTLParser.AtomExprContext):
        self.ref_atomics.append(ctx.getText())


    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        self.bound_atomics.append(ctx.atomicIdentifier().getText())
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#mapping.
    def visitMapping(self, ctx:MLTLParser.MappingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#formulaIdentifier.
    def visitFormulaIdentifier(self, ctx:MLTLParser.FormulaIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#atomicIdentifier.
    def visitAtomicIdentifier(self, ctx:MLTLParser.AtomicIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#signalIdentifier.
    def visitSignalIdentifier(self, ctx:MLTLParser.SignalIdentifierContext):
        return self.visitChildren(ctx)
