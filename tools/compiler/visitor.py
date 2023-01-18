# type: ignore

from logging import getLogger

from antlr4 import TerminalNode

from .parser.C2POVisitor import C2POVisitor
from .parser.C2POParser import C2POParser
from .ast import *
from .util import *

logger = getLogger(logger_name)

class Visitor(C2POVisitor):

    def __init__(self) -> None:
        super().__init__()
        self.structs: StructDict = {}
        self.vars: dict[str,Type] = {}
        self.defs: dict[str,AST] = {}
        self.spec_num: int = 0
        self.status = True

        # Initialize special structs/functions
        self.structs['Set'] = {'set':NOTYPE(),'size':UINT64()}


    def error(self, msg) -> None:
        logger.error(msg)
        self.status = False

    
    def warning(self, msg) -> None:
        logger.warning(msg)


    # Visit a parse tree produced by C2POParser#start.
    def visitStart(self, ctx:C2POParser.StartContext) -> list[Program]:
        ln: int = ctx.start.line 

        for s in ctx.struct_block():
            self.visit(s)
        for v in ctx.input_block():
            self.visit(v)
        for d in ctx.def_block():
            self.visit(d)

        ret: list[Program] = []
        for s in ctx.spec_block():
            ret.append(self.visit(s))

        if len(ret) < 1:
            self.error(f'{ln}: No specifications provided.') 

        return ret


    # Visit a parse tree produced by C2POParser#struct_block.
    def visitStruct_block(self, ctx:C2POParser.Struct_blockContext):
        ln: int = ctx.start.line 

        for s in ctx.struct():
            self.visit(s)


    # Visit a parse tree produced by C2POParser#struct.
    def visitStruct(self, ctx:C2POParser.StructContext) -> None:
        ln: int = ctx.start.line 

        id: str = ctx.SYMBOL().getText()
        if id in self.structs.keys():
            self.warning(f'{ln}: Struct {i} already defined, redefining')

        self.structs[id] = {}
        var_dict: dict[str,Type] = {}
        for vl in ctx.var_list():
            var_dict = self.visit(vl)
            self.structs[id].update(var_dict)


    # Visit a parse tree produced by C2POParser#input_block.
    def visitInput_block(self, ctx:C2POParser.Input_blockContext):
        ln: int = ctx.start.line

        var_dict: dict[str,Type]
        for vl in ctx.var_list():
            var_dict = self.visit(vl)

            for id in var_dict.keys():
                if id in self.vars.keys():
                    self.error(f'{ln}: Variable {id} declared more than once')

            self.vars.update(var_dict)


    # Visit a parse tree produced by C2POParser#var_list.
    def visitVar_list(self, ctx:C2POParser.Var_listContext) -> dict[str,Type]:
        ln: int = ctx.start.line
        var_type: Type = self.visit(ctx.type_())

        id: TerminalNode
        var_dict: dict[str,Type] = {}
        for id in ctx.SYMBOL():
            if id in var_dict.keys():
                self.error(f'{ln}: Variable {id} declared more than once')
            var_dict[id.getText()] = var_type

        return var_dict


    # Visit a parse tree produced by C2POParser#type.
    def visitType(self, ctx:C2POParser.TypeContext) -> Type:
        ln: int = ctx.start.line
        id: str = ctx.SYMBOL().getText()

        if id == 'bool':
            return BOOL()
        elif id == 'int8':
            return INT8()
        elif id == 'int16':
            return INT16()
        elif id == 'int32':
            return INT32()
        elif id == 'int64':
            return INT64()
        elif id == 'uint8':
            return UINT8()
        elif id == 'uint16':
            return UINT16()
        elif id == 'uint32':
            return UINT32()
        elif id == 'uint64':
            return UINT64()
        elif id == 'float':
            return FLOAT()
        elif id == 'double':
            return DOUBLE()
        elif id == 'set':
            t: Type = self.visit(ctx.type_())
            return SET(t)
        elif id in self.structs.keys():
            return STRUCT(id)

        self.error(f'{ln}: Type \'{ctx.getText()}\' not recognized')
        return NoType()


    # Visit a parse tree produced by C2POParser#def_block.
    def visitDef_block(self, ctx:C2POParser.Def_blockContext) -> None:
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def.
    def visitDef(self, ctx:C2POParser.DefContext) -> None:
        ln: int = ctx.start.line
        var: str = ctx.SYMBOL().getText()
        expr: AST = self.visit(ctx.expr())

        if var in self.vars.keys():
            self.error(f'{ln}: Variable \'{var}\' already declared')
        elif var in self.defs.keys():
            self.warning(f'{ln}: Variable \'{var}\' defined twice, using most recent definition')
            self.defs[var] = expr
        else:
            self.defs[var] = expr


    # Visit a parse tree produced by C2POParser#spec_block.
    def visitSpec_block(self, ctx:C2POParser.Spec_blockContext) -> Program:
        ln: int = ctx.start.line
        specs: list[Specification]
        spec_dict: dict[int,Specification] = {}
        contract_dict: dict[int,Specification] = {}

        self.spec_num = 0

        for s in ctx.spec():
            specs = self.visit(s)

            if len(specs) > 1: # then s is a contract
                contract_dict[self.spec_num] = specs[0]

            for sp in specs:
                spec_dict[self.spec_num] = sp
                self.spec_num += 1

        return Program(ln, self.structs, spec_dict, contract_dict)


    # Visit a parse tree produced by C2POParser#spec.
    def visitSpec(self, ctx:C2POParser.SpecContext) -> list[Specification]:
        ln: int = ctx.start.line
        label: str = ''

        if ctx.expr():
            expr: AST = self.visit(ctx.expr())
        
            # if spec has a label, can be referred to in other specs
            # else, cannot be referred to later, do not store
            if ctx.SYMBOL(): 
                label = ctx.SYMBOL().getText()
                if label in list(self.defs):
                    self.warning(f'{ln}: Spec label identifier \'{label}\' previously declared, not storing')
                else:
                    self.defs[label] = expr

            return [Specification(ln, label, self.spec_num, expr)]
        else:
            f1,f2,f3 = self.visit(ctx.contract())
            label = ctx.SYMBOL().getText()

            return [Specification(ln, label, self.spec_num, f1),
                    Specification(ln, label, self.spec_num+1, f2),
                    Specification(ln, label, self.spec_num+2, f3)]


    # Visit a parse tree produced by C2POParser#contract.
    def visitContract(self, ctx:C2POParser.ContractContext) -> list[AST]:
        ln: int = ctx.start.line
        lhs: AST = self.visit(ctx.expr(0))
        rhs: AST = self.visit(ctx.expr(1))

        f1: AST = lhs
        f2: AST = LogicalImplies(ln,lhs,rhs)
        f3: AST = LogicalAnd(ln,lhs,rhs)

        return [f1,f2,f3]


    # Visit a parse tree produced by C2POParser#LogBinExpr.
    def visitLogBinExpr(self, ctx:C2POParser.LogBinExprContext) -> AST:
        ln: int = ctx.start.line
        lhs: AST = self.visit(ctx.expr(0))
        rhs: AST = self.visit(ctx.expr(1))

        if ctx.LOG_OR():
            return LogicalOr(ln, [lhs, rhs])
        elif ctx.LOG_AND():
            return LogicalAnd(ln, [lhs, rhs])
        elif ctx.LOG_XOR():
            return LogicalXor(ln, lhs, rhs)
        elif ctx.LOG_IMPL():
            return LogicalImplies(ln, lhs, rhs)
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#TLBinExpr.
    def visitTLBinExpr(self, ctx:C2POParser.TLBinExprContext) -> AST:
        ln: int = ctx.start.line
        lhs: AST = self.visit(ctx.expr(0))
        rhs: AST = self.visit(ctx.expr(1))
        bounds: Interval = self.visit(ctx.tl_op().interval())

        if ctx.tl_op():
            op: str = ctx.tl_op().SYMBOL().getText()
            if op == 'U':
                return Until(ln, lhs, rhs, bounds.lb, bounds.ub)
            elif op == 'R':
                return Release(ln, lhs, rhs, bounds.lb, bounds.ub)
            elif op == 'S':
                return Since(ln, lhs, rhs, bounds.lb, bounds.ub)
            else:
                self.error(f'{ln}: Binary TL op \'{ctx.tl_op().SYMBOL().getText()}\' not recognized')
                return AST(ln, [])
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#TLUnaryExpr.
    def visitTLUnaryExpr(self, ctx:C2POParser.TLUnaryExprContext) -> AST:
        ln: int = ctx.start.line
        operand: AST = self.visit(ctx.expr())
        bounds: Interval = self.visit(ctx.tl_op().interval())

        if ctx.tl_op():
            op: str = ctx.tl_op().SYMBOL().getText()
            if op == 'G':
                return Global(ln, operand, bounds.lb, bounds.ub)
            elif op == 'F':
                return Future(ln, operand, bounds.lb, bounds.ub)
            elif op == 'H':
                return Historical(ln, operand, bounds.lb, bounds.ub)
            elif op == 'O':
                return Once(ln, operand, bounds.lb, bounds.ub)
            else:
                self.error(f'{ln}: Unary TL op \'{ctx.tl_op().SYMBOL().getText()}\' not recognized')
                return AST(ln, [])
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext) -> AST:
        return self.visit(ctx.expr())


    # Visit a parse tree produced by C2POParser#TernaryExpr.
    def visitTernaryExpr(self, ctx:C2POParser.TernaryExprContext) -> AST:
        self.error(f'{ln}: Ternary operator \'{ctx.getText()}\' not supported')
        return AST(ln, [])


    # Visit a parse tree produced by C2POParser#BWExpr.
    def visitBWExpr(self, ctx:C2POParser.BWExprContext) -> AST:
        ln: int = ctx.start.line
        lhs: AST = self.visit(ctx.expr(0))
        rhs: AST = self.visit(ctx.expr(1))

        if ctx.BW_OR():
            return BitwiseOr(ln, lhs, rhs)
        elif ctx.BW_XOR():
            return BitwiseXor(ln, lhs, rhs)
        elif ctx.BW_AND():
            return BitwiseAnd(ln, lhs, rhs)
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return AST(ln, [])
            

    # Visit a parse tree produced by C2POParser#RelExpr.
    def visitRelExpr(self, ctx:C2POParser.RelExprContext) -> AST:
        ln: int = ctx.start.line
        lhs: AST = self.visit(ctx.expr(0))
        rhs: AST = self.visit(ctx.expr(1))

        if ctx.rel_eq_op():
            if ctx.rel_eq_op().REL_EQ():
                return Equal(ln, lhs, rhs)
            elif ctx.rel_eq_op().REL_NEQ:
                return NotEqual(ln, lhs, rhs)
            else:
                self.error(f'{ln}: Rel op \'{ctx.rel_eq_op().start.text}\' not recognized')
                return AST(ln, [])
        elif ctx.rel_ineq_op():
            if ctx.rel_ineq_op().REL_GT():
                return GreaterThan(ln, lhs, rhs)
            elif ctx.rel_ineq_op().REL_LT():
                return LessThan(ln, lhs, rhs)
            elif ctx.rel_ineq_op().REL_GTE():
                return GreaterThanOrEqual(ln, lhs, rhs)
            elif ctx.rel_ineq_op().REL_LTE():
                return LessThanOrEqual(ln, lhs, rhs)
            else:
                self.error(f'{ln}: Rel op \'{ctx.rel_ineq_op().start.text}\' not recognized')
                return AST(ln, [])
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#ArithAddExpr.
    def visitArithAddExpr(self, ctx:C2POParser.ArithAddExprContext) -> AST:
        ln: int = ctx.start.line
        lhs: AST = self.visit(ctx.expr(0))
        rhs: AST = self.visit(ctx.expr(1))

        if ctx.arith_add_op():
            if ctx.arith_add_op().ARITH_ADD():
                return ArithmeticAdd(ln, lhs, rhs)
            elif ctx.arith_add_op().ARITH_SUB():
                return ArithmeticSubtract(ln, lhs, rhs)
            else:
                self.error(f'{ln}: Unary TL op \'{ctx.tl_unary_op().start.text}\' not recognized')
                return AST(ln, [])
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#ArithMulExpr.
    def visitArithMulExpr(self, ctx:C2POParser.ArithMulExprContext) -> AST:
        ln: int = ctx.start.line
        lhs: AST = self.visit(ctx.expr(0))
        rhs: AST = self.visit(ctx.expr(1))

        if ctx.arith_mul_op():
            if ctx.arith_mul_op().ARITH_MUL():
                return ArithmeticMultiply(ln, lhs, rhs)
            elif ctx.arith_mul_op().ARITH_DIV():
                return ArithmeticDivide(ln, lhs, rhs)
            elif ctx.arith_mul_op().ARITH_MOD():
                return ArithmeticModulo(ln, lhs, rhs)
            else:
                self.error(f'{ln}: Binary arithmetic op \'{ctx.tl_bin_op().start.text}\' not recognized')
                return AST(ln, [])
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#UnaryExpr.
    def visitUnaryExpr(self, ctx:C2POParser.UnaryExprContext) -> AST:
        ln: int = ctx.start.line
        op: AST = self.visit(ctx.expr())

        if ctx.ARITH_SUB():
            return ArithmeticNegate(ln, op)
        elif ctx.BW_NEG():
            return BitwiseNegate(ln, op)
        elif ctx.LOG_NEG():
            return LogicalNegate(ln, op)
        else:
            self.error(f'{ln}: Unary op \'{ctx.unary_op().start.text}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#FuncExpr.
    def visitFuncExpr(self, ctx:C2POParser.FuncExprContext) -> AST:
        ln: int = ctx.start.line
        id: str = ctx.SYMBOL().getText()
        expr_list: list[AST] = self.visit(ctx.expr_list())

        if id in self.structs.keys():

            # if id == 'Set':
            #     expr_list[0].set_dynamic_set_size()

            members: dict[str,AST] = {}
            if len(expr_list) == len(self.structs[id]):
                for s in self.structs[id].keys():
                    members[s] = expr_list.pop(0)
                return Struct(ln,id,members)
            else:
                self.error(f'{ln}: Member mismatch for struct \'{id}\', number of members do not match')
                return AST(ln, [])
        else:
            self.error(f'{ln}: Symbol \'{id}\' not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#SetAggExpr.
    def visitSetAggExpr(self, ctx:C2POParser.SetAggExprContext) -> AST:
        ln: int = ctx.start.line
        op: str = ctx.SYMBOL().getText()

        S,v = self.visit(ctx.set_agg_binder())
        self.defs[v.name] = v
        e1: AST
        if len(ctx.expr()) == 1:
            e1 = self.visit(ctx.expr(0))
        else:
            e1 = self.visit(ctx.expr(1))
        del self.defs[v.name]

        if op == 'foreach':
            if len(ctx.expr()) != 1:
                self.error(f'{ln}: Extra parameter given for set aggregation expression \'{ctx.getText()}\'')
            return ForEach(ln,S,v,e1)
        elif op == 'forsome':
            return ForSome(ln,S,v,e1)
        elif op == 'forexactlyn':
            if len(ctx.expr()) > 1:
                n: AST = self.visit(ctx.expr(0))
                return ForExactlyN(ln,S,n,v,e1)
            else:
                self.error(f'{ln}: No parameter \'n\' for set aggregation expression \'{ctx.getText()}\'')
        elif op == 'foratleastn':
            if len(ctx.expr()) > 1:
                n: AST = self.visit(ctx.expr(0))
                return ForAtLeastN(ln,S,n,v,e1)
            else:
                self.error(f'{ln}: No parameter \'n\' for set aggregation expression \'{ctx.getText()}\'')
        elif op == 'foratmostn':
            if len(ctx.expr()) > 1:
                n: AST = self.visit(ctx.expr(0))
                return ForAtMostN(ln,S,n,v,e1)
            else:
                self.error(f'{ln}: No parameter \'n\' for set aggregation expression \'{ctx.getText()}\'')
        else:
            self.error(f'{ln}: Set aggregation operator \'{op}\' not supported')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#set_agg_binder.
    def visitSet_agg_binder(self, ctx:C2POParser.Set_agg_binderContext) -> tuple[AST,Variable]:
        ln: int = ctx.start.line
        S: AST = self.visit(ctx.expr())
        v: Variable = Variable(ln,ctx.SYMBOL().getText())
        return (S,v)


    # Visit a parse tree produced by C2POParser#StructMemberExpr.
    def visitStructMemberExpr(self, ctx:C2POParser.StructMemberExprContext) -> AST:
        ln: int = ctx.start.line
        id: str = ctx.SYMBOL().getText()
        e: AST = self.visit(ctx.expr())
        return StructAccess(ln,e,id)


    # Visit a parse tree produced by C2POParser#SetExpr.
    def visitSetExpr(self, ctx:C2POParser.SetExprContext) -> AST:
        ln: int = ctx.start.line
        elements: list[AST] = []
        
        if ctx.set_expr().expr_list():
            elements = self.visit(ctx.set_expr().expr_list())

        return Set(ln, len(elements), elements)


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext) -> AST:
        return self.visit(ctx.expr())


    # Visit a parse tree produced by C2POParser#LiteralExpr.
    def visitLiteralExpr(self, ctx:C2POParser.LiteralExprContext) -> AST:
        ln: int = ctx.start.line

        literal: C2POParser.LiteralContext = ctx.literal()

        if literal.SYMBOL():
            name: str = literal.SYMBOL().getText()
            if name == 'true':
                return Bool(ln, True)
            elif name == 'false':
                return Bool(ln, False)
            elif name in self.defs.keys():
                return self.defs[name]
            elif name in self.vars.keys():
                return Signal(ln, name, self.vars[name])
            else:
                self.error(f'{ln}: Variable \'{name}\' undefined')
                return AST(ln, [])
        elif literal.INT():
            return Integer(ln, int(literal.INT().getText()))
        elif literal.FLOAT():
            return Float(ln, float(literal.FLOAT().getText()))
        else:
            self.error(f'{ln}: Literal \'{ctx.start.text}\' parser token not recognized')
            return AST(ln, [])


    # Visit a parse tree produced by C2POParser#interval.
    def visitInterval(self, ctx:C2POParser.IntervalContext) -> Interval:
        ln: int = ctx.start.line
        bounds = ctx.INT()

        if len(bounds) == 1:
            u: int = int(bounds[0].getText())
            return Interval(lb=0,ub=u)
        elif len(bounds) == 2:
            l: int = int(bounds[0].getText())
            u: int = int(bounds[1].getText())
            return Interval(lb=l,ub=u)
        else:
            self.error(f'{ln}: Expression \'{ctx.getText()}\' not recognized')
            return Interval(0,0)


        # Visit a parse tree produced by C2POParser#expr_list.
    def visitExpr_list(self, ctx:C2POParser.Expr_listContext) -> list[AST]:
        ln: int = ctx.start.line
        exprs: list[AST] = []

        for expr in ctx.expr():
            e: AST = self.visit(expr)
            exprs.append(e)

        return exprs


del C2POParser