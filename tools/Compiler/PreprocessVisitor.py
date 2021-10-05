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
        * resolve filter arguments -- names of sets vs. signals vs. numbers
    """

    def __init__(self):
        self.atomics = {}
        self.literal_atomics = set()
        self.named_atomics = set()
        self.bound_atomics = set()
        self.supp_bindings = set()
        self.filter_args = set()
        self.literal_signals = set()
        self.named_signals = set()
        self.mapped_signals = set()
        self.def_sets = set()
        self.supp_mappings = []
        self.formula_labels = []
        self.contracts = {}
        self.num_ft = 0
        self.num_pt = 0
        self.is_ft = False # track if expr is part of FT expr
        self.is_pt = False # track if expr is part of PT expr
        self.ft = ''
        self.pt = ''
        self.status = True


    def visitErrorNode(self, node):
        self.status = False


    # Visit a parse tree produced by MLTLParser#program.
    def visitProgram(self, ctx:MLTLParser.ProgramContext):
        self.visitChildren(ctx)

        # resolve atomics -- any referenced, unbound atomic must be bound to some
        # default boolean value
        for atomic in self.literal_atomics:
            if atomic not in self.bound_atomics:
                idx = re.search('\d+',atomic).group()
                self.supp_bindings.add('a'+idx+' := bool(s'+idx+') == 1;')

        # error if there are  any named, unbound atomics
        for atomic in self.named_atomics:
            if atomic not in self.bound_atomics:
                print('ERROR: atomic referenced but not bound \''+atomic+'\'')
                self.status = False

        # resolve signals

        # error if any used filter args are undefined (excluding literals)
        for arg in self.filter_args:
            if not (arg in self.def_sets or arg in self.mapped_signals or arg in self.literal_signals):
                print('ERROR: filter argument undefined \'' + arg + '\'')
                self.status = False

        return


    # Visit a parse tree produced by MLTLParser#statement.
    def visitStatement(self, ctx:MLTLParser.StatementContext):
        self.visitChildren(ctx)

        # handle expressions -- keep track of formula numbers, reset 
        # whether expr is of type FT/PT, and split up FT/PT formulas
        # PROBLEM: cannot consistently keep track of line numbers with comments
        # what's the spec on formula numbering exactly?
        if self.status:
            if ctx.expr():
                if self.is_pt:
                    self.num_pt += 1
                    self.is_pt = False
                    self.pt += ctx.getText()+'\n'
                    self.ft += '\n'
                else:
                    self.num_ft += 1
                    self.is_ft = False
                    self.pt += '\n'
                    self.ft += ctx.getText()+'\n'
            else:
                self.pt += '\n'
                self.ft += '\n'
        


    # Visit a parse tree produced by MLTLParser#contract.
    def visitContract(self, ctx:MLTLParser.ContractContext):
        label = ctx.Identifier()
        if not label:
            cnum = 1
            while(True):
                if 'c'+str(cnum) not in self.contracts.keys():
                    name = 'c'+str(cnum)
                    break
                cnum += 1
        else:
            name = label.getText()
        
        self.contracts[name] = [ctx.expr(0).getText(), ctx.expr(1).getText()]


    # Visit a parse tree produced by MLTLParser#PropExpr.
    def visitPropExpr(self, ctx:MLTLParser.PropExprContext):
        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#BoolExpr.
    def visitBoolExpr(self, ctx:MLTLParser.BoolExprContext):
        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#UnaryTemporalExpr.
    def visitUnaryTemporalExpr(self, ctx:MLTLParser.UnaryTemporalExprContext):
        if ctx.UnaryTemporalOp().getText() == 'G' or ctx.UnaryTemporalOp().getText() == 'F':
            if self.is_pt:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.is_ft = True
            self.visitChildren(ctx)
        else: # unary operator is PT (H or O)
            if self.is_ft:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.is_pt = True
            self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#BinaryTemporalExpr.
    def visitBinaryTemporalExpr(self, ctx:MLTLParser.BinaryTemporalExprContext):
        if ctx.BinaryTemporalOp().getText() == 'U' or ctx.BinaryTemporalOp().getText() == 'R':
            if self.is_pt:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.is_ft = True
            self.visitChildren(ctx)
        else: # binary operator is PT (Y or S)
            if self.is_ft:
                print('ERROR: mixed time operators used in formula ' + ctx.getText())
                self.status = False
                return

            self.is_pt = True
            self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#ParensExpr.
    def visitParensExpr(self, ctx:MLTLParser.ParensExprContext):
        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#AtomExpr.
    def visitAtomExpr(self, ctx:MLTLParser.AtomExprContext):
        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        atomIdent = ctx.atomicIdentifier().getText()
        if atomIdent in self.bound_atomics:
            print('WARNING: atomic already bound \'' + atomIdent + '\', rebinding')
        self.bound_atomics.add(atomIdent)

        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#mapping.
    def visitMapping(self, ctx:MLTLParser.MappingContext):
        sigIdent = ctx.signalIdentifier().getText()
        if sigIdent in self.mapped_signals:
            print('WARNING: signal already mapped \'' + sigIdent + '\', remapping')
        self.mapped_signals.add(sigIdent)

        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#setAssignment.
    def visitSetAssignment(self, ctx:MLTLParser.SetAssignmentContext):
        setIdent = ctx.setIdentifier().getText()
        if setIdent in self.def_sets:
            print('WARNING: set already defined \'' + setIdent + '\', redefining')
        self.mapped_signals.add(setIdent)

        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#filterArgument.
    def visitFilterArgument(self, ctx:MLTLParser.FilterArgumentContext):
        self.filter_args.add(ctx.getText())

        # since this token is not a signalIdentifier, need to manually handle this case
        if ctx.LiteralSignalIdentifier():
            self.literal_signals.add(ctx.LiteralSignalIdentifier().getText())

        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#formulaIdentifier.
    def visitFormulaIdentifier(self, ctx:MLTLParser.FormulaIdentifierContext):
        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#setIdentifier.
    def visitSetIdentifier(self, ctx:MLTLParser.SetIdentifierContext):
        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#filterIdentifier.
    def visitFilterIdentifier(self, ctx:MLTLParser.FilterIdentifierContext):
        self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#atomicIdentifier.
    def visitAtomicIdentifier(self, ctx:MLTLParser.AtomicIdentifierContext):
        if ctx.LiteralAtomicIdentifier():
            self.literal_atomics.add(ctx.LiteralAtomicIdentifier().getText())
        else:
            self.named_atomics.add(ctx.Identifier().getText())


    # Visit a parse tree produced by MLTLParser#signalIdentifier.
    def visitSignalIdentifier(self, ctx:MLTLParser.SignalIdentifierContext):
        if ctx.LiteralSignalIdentifier():
            self.literal_signals.add(ctx.LiteralSignalIdentifier().getText())
        else:
            self.named_signals.add(ctx.Identifier().getText())
