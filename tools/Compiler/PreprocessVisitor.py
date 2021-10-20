from .MLTLVisitor import MLTLVisitor
from .MLTLParser import MLTLParser

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
        self.filter_args = set()
        self.signals = {}
        self.literal_signals = set()
        self.named_signals = set()
        self.mapped_signals = set()
        self.def_sets = {}
        self.formula_labels = {}
        self.contracts = {}
        self.contract_formula_nums = {}
        self.num_ft = 0
        self.num_pt = 0
        self.is_ft = False # track if expr is part of FT expr
        self.is_pt = False # track if expr is part of PT expr
        self.ft = ''
        self.pt = ''
        self.at = ''
        self.status = True


    def visitErrorNode(self, node):
        self.status = False


    # Visit a parse tree produced by MLTLParser#program.
    def visitProgram(self, ctx:MLTLParser.ProgramContext):
        self.visitChildren(ctx)

        # resolve atomics -- any referenced, unbound, literal atomic must be bound 
        # to some default boolean value
        # assign atomic index referenced in value
        for atomic in self.literal_atomics:
            idx = re.search('\d+',atomic).group()
            if atomic not in self.bound_atomics:
                self.at += 'a'+idx+'=bool(s'+idx+')==1;\n'
            self.atomics[atomic] = idx

        # error if there are any named, unbound atomics
        # assign atomic a valid index
        idx = -1
        for atomic in self.named_atomics:
            if atomic not in self.bound_atomics:
                print('ERROR: named atomic referenced but not bound \''+atomic+'\'')
                self.status = False
            idx += 1
            while 'a'+str(idx) in self.atomics.keys():
                idx += 1
            self.atomics[atomic] = idx

        # resolve signals -- any referenced, unmapped, literal signal must be bound 
        # to some default signal value
        for signal in self.literal_signals:
            idx = re.search('\d+',signal).group()
            self.signals[signal] = idx

        # error if there are any named, unmapped signals
        idx = -1
        for signal in self.named_signals:
            if signal not in self.mapped_signals:
                print('ERROR: named signal referenced but not mapped \''+signal+'\'')
                self.status = False
            idx += 1
            while 's'+str(idx) in self.signals.keys():
                idx += 1
            self.signals[signal] = idx

        # configure contract formulas
        # append antecedent, consquent, and their conjunction to FT/PT
        for name, expr in self.contracts.items():
            if expr[2]: # is_ft == true
                self.ft += expr[0]+';\n'
                self.ft += expr[1]+';\n'
                self.ft += '('+expr[0]+')&('+expr[1]+');\n'
                self.pt += ';\n;\n;\n'
                # keep track of formula numbers
                ft_len = len(self.ft.splitlines())
                self.contract_formula_nums[name] = ft_len-2
            else: # is_pt == true
                self.pt += expr[0]+';\n'
                self.pt += expr[1]+';\n'
                self.pt += '('+expr[0]+')&('+expr[1]+');\n'
                self.ft += ';\n;\n;\n'
                # keep track of formula numbers
                pt_len = len(self.pt.splitlines())
                self.contract_formula_nums[name] = pt_len-2

        # error if any used filter args are undefined (excluding literals)
        for arg in self.filter_args:
            if not (arg in self.def_sets or arg in self.mapped_signals or arg in self.literal_signals):
                print('ERROR: filter argument undefined \'' + arg + '\'')
                self.status = False

        # resolve atomics in defined sets
        for setIdent in self.def_sets.keys():
            atomics = self.def_sets[setIdent][1]
            for atom, idx in self.atomics.items():
                if atom in atomics:
                    atomics.remove(atom)
                    atomics.append('a'+str(idx))


    # Visit a parse tree produced by MLTLParser#statement.
    def visitStatement(self, ctx:MLTLParser.StatementContext):
        self.visitChildren(ctx)

        # handle expressions -- keep track of formula numbers, reset 
        # whether expr is of type FT/PT, and split up FT/PT formulas
        if self.status and ctx.expr():
            if self.is_pt:
                self.num_pt += 1
                self.is_pt = False
                self.pt += ctx.getText()+';\n'
                self.ft += ';\n'
            else:
                self.num_ft += 1
                self.is_ft = False
                self.pt += ';\n'
                self.ft += ctx.getText()+';\n'
        elif self.status and ctx.binding():
            # maintain list of AT instructions
            self.at += ctx.getText()+';\n'


    # Visit a parse tree produced by MLTLParser#contract.
    def visitContract(self, ctx:MLTLParser.ContractContext):
        label = ctx.formulaIdentifier()
        if not label:
            cnum = 1
            while(True):
                if 'c'+str(cnum) not in self.contracts.keys():
                    name = 'c'+str(cnum)
                    break
                cnum += 1
        else:
            name = label.getText()

        self.visit(ctx.expr(0))
        self.visit(ctx.expr(1))
        is_ft = (self.is_ft or (not self.is_ft and not self.is_pt))

        self.is_ft = False
        self.is_pt = False
        
        self.contracts[name] = [ctx.expr(0).getText(), ctx.expr(1).getText(), is_ft]


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
        if setIdent in self.def_sets.keys():
            print('WARNING: set already defined \'' + setIdent + '\', redefining')

        atomics = []
        atomicIdents = ctx.atomicIdentifier()
        for atom in atomicIdents:
            atomics.append(atom.getText())
        self.def_sets[setIdent] = [len(self.def_sets),atomics]

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
        self.formula_labels[ctx.getText()] = ctx.start.line-1


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
