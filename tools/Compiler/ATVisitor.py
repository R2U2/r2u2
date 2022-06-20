from .MLTLVisitor import MLTLVisitor
from .MLTLParser import MLTLParser

class ATVisitor(MLTLVisitor):

    def __init__(self, atomics, signals, filters, def_sets):
        self.atomics = atomics
        self.signals = signals
        self.filters = filters
        self.def_sets  = def_sets
        self.at_instr = {}

    
    # Visit a parse tree produced by MLTLParser#program.
    def visitProgram(self, ctx:MLTLParser.ProgramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#statement.
    def visitStatement(self, ctx:MLTLParser.StatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MLTLParser#binding.
    def visitBinding(self, ctx:MLTLParser.BindingContext):
        atomIdent = ctx.atomicIdentifier().getText()
        atom = self.atomics[atomIdent]

        filter = ctx.filterIdentifier().getText()
        if filter not in self.filters:
            print('ERROR: using unknown AT filter in binding ' + ctx.getText())

        cond = ctx.Conditional().getText()

        comp = ''
        if ctx.Number():
            comp = ctx.Number().getText()
        else:
            compIdent = ctx.signalIdentifier().getText()
            comp = 's'+str(self.signals[compIdent])

        args = []
        for arg in ctx.filterArgument():
            argIdent = arg.getText()
            if argIdent in self.atomics.keys(): 
                # arg is an atomic, resolve
                args.append('a'+str(self.atomics[argIdent]))
            elif argIdent in self.signals.keys():
                # arg is an signal, resolve
                args.append('s'+str(self.signals[argIdent]))
            elif argIdent in self.def_sets.keys():
                # arg is a set, resolve
                args.append('r'+str(self.def_sets[argIdent][0]))
            else:
                # else arg is a const
                args.append(argIdent)

        self.at_instr[atom] = [filter, cond, comp, args]

        return self.visitChildren(ctx)



del MLTLParser