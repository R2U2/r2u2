from .MLTLVisitor import MLTLVisitor
from .MLTLParser import MLTLParser

class ATVisitor(MLTLVisitor):

    def __init__(self, filters):
        self.filters = filters
        self.at_instr = {}
    
    # Visit a parse tree produced by MLTLParser#program.
    def visitProgram(self, ctx:MLTLParser.ProgramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#statement.
    def visitStatement(self, ctx:MLTLParser.StatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        atom = ctx.atomicIdentifier().getText()

        filter = ctx.filterIdentifier().getText()
        if filter not in self.filters:
            print('ERROR: using unkown AT filter in binding ' + ctx.getText())

        signal = ctx.filterArgument(0).getText()

        args = []
        i = 1
        while ctx.filterArgument(i):
            args.append(ctx.filterArgument(i).getText())

        cond = ctx.Conditional().getText()

        comp = ''
        if ctx.Number():
            comp = ctx.Number().getText()
        else:
            comp = ctx.signalIdentifier().getText()

        self.at_instr[atom] = [filter, signal, args, cond, comp]

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