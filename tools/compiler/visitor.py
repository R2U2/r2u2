from antlr4 import TerminalNode

from .parser.C2POVisitor import C2POVisitor
from .parser.C2POParser import C2POParser

from .ast import *

class Visitor(C2POVisitor):

    def __init__(self) -> None:
        super().__init__()
        self.vars: dict[str,Type] = {}
        self.defs: dict[str,EXPR] = {}
        self.order: dict[str,int] = {}
        self.spec_num: int = 0
        

    # Visit a parse tree produced by C2POParser#start.
    def visitStart(self, ctx:C2POParser.StartContext) -> list[PROGRAM]:
        for v in ctx.var_block():
            self.visit(v)
        for d in ctx.def_block():
            self.visit(d)

        ret: list[PROGRAM] = []
        for s in ctx.spec_block():
            ret.append(self.visit(s))
        return ret


    # Visit a parse tree produced by C2POParser#var_block.
    def visitVar_block(self, ctx:C2POParser.Var_blockContext) -> None:
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#var_list.
    def visitVar_list(self, ctx:C2POParser.Var_listContext) -> None:
        var_type: Type = self.visit(ctx.type_())

        id: TerminalNode
        for id in ctx.IDENTIFIER():
            self.vars[id.getText()] = var_type

    
    # Visit a parse tree produced by C2POParser#order_list.
    def visitOrder_list(self, ctx:C2POParser.Order_listContext):
        var_list: list[str] = list(self.vars)
        sid: int = 0
        id: TerminalNode
        for id in ctx.IDENTIFIER():
            if not id.getText() in var_list:
                sid += 1 # error?
            elif id.getText() == '_':
                sid += 1
            else:
                self.order[id.getText()] = sid
                sid += 1


    # Visit a parse tree produced by C2POParser#type.
    def visitType(self, ctx:C2POParser.TypeContext) -> Type:
        text = ctx.getText()

        if text == 'bool':
            return Type.BOOL
        elif text == 'int':
            return Type.INT
        elif text == 'float':
            return Type.FLOAT
        # elif ctx.KW_SET:
        #     return Type._SET

        raise RuntimeError


    # Visit a parse tree produced by C2POParser#set_param.
    def visitSet_param(self, ctx:C2POParser.Set_paramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def_block.
    def visitDef_block(self, ctx:C2POParser.Def_blockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def_list.
    def visitDef_list(self, ctx:C2POParser.Def_listContext):
        var: str = ctx.IDENTIFIER().getText()
        expr: EXPR = self.visit(ctx.expr())
        self.defs[var] = expr


    # Visit a parse tree produced by C2POParser#spec_block.
    def visitSpec_block(self, ctx:C2POParser.Spec_blockContext) -> PROGRAM:
        spec: SPEC
        spec_label: str
        spec_dict: dict[tuple[int,str],SPEC] = {}

        self.spec_num = 0

        for s in ctx.spec():
            spec = self.visit(s)

            if s.IDENTIFIER():
                spec_label = s.IDENTIFIER().getText()
            else:
                spec_label = "s"+str(self.spec_num)

            spec_dict[(self.spec_num, spec_label)] = spec
            self.spec_num += 1

        return PROGRAM(spec_dict,self.order)


    # Visit a parse tree produced by C2POParser#spec.
    def visitSpec(self, ctx:C2POParser.SpecContext) -> SPEC:
        lineno: int = ctx.start.line
        expr: EXPR = self.visit(ctx.expr())
        label: str = ''

        # if spec has a label, can be referred to in other specs
        # else, cannot be referred to later, do not store
        if ctx.IDENTIFIER(): 
            label = ctx.IDENTIFIER().getText()
            self.defs[label] = expr

        return SPEC(label, self.spec_num, expr)



    # Visit a parse tree produced by C2POParser#LitExpr.
    def visitLitExpr(self, ctx:C2POParser.LitExprContext) -> EXPR:
        lineno: int = ctx.start.line

        if ctx.log_lit():
            return ctx.log_lit().visit()
        elif ctx.IDENTIFIER():
            name: str = ctx.IDENTIFIER().getText()
            if name in list(self.defs):
                return self.defs[name]
            else:
                return VAR(name, self.vars[name])
        elif ctx.INT():
            return INT(int(ctx.INT().getText()))
        elif ctx.FLOAT():
            return FLOAT(float(ctx.FLOAT().getText()))
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#log_lit.
    def visitLog_lit(self, ctx:C2POParser.Log_litContext) -> EXPR:
        lineno: int = ctx.start.line

        if ctx.TRUE():
            return BOOL(True)
        elif ctx.FALSE():
            return BOOL(False)
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext) -> EXPR:
        return self.visit(ctx.expr())


    # Visit a parse tree produced by C2POParser#TLBinExpr.
    def visitTLBinExpr(self, ctx:C2POParser.TLBinExprContext):
        lineno: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))
        bounds: Interval = self.visit(ctx.interval())

        if ctx.tl_bin_op():
            if ctx.tl_bin_op().TL_UNTIL():
                return TL_UNTIL(lhs, rhs, bounds.lb, bounds.ub)
            elif ctx.tl_bin_op().TL_RELEASE():
                return LOG_NEG(TL_RELEASE(LOG_NEG(lhs), LOG_NEG(rhs), bounds.lb, bounds.ub))
            elif ctx.tl_bin_op().TL_SINCE():
                return TL_SINCE(lhs, rhs, bounds.lb, bounds.ub)
            else:
                raise RuntimeError
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#LogBinExpr.
    def visitLogBinExpr(self, ctx:C2POParser.LogBinExprContext) -> EXPR:
        lineno: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.LOG_OR():
            return LOG_NEG(LOG_AND(LOG_NEG(lhs), LOG_NEG(rhs)))
        elif ctx.LOG_AND():
            return LOG_AND(lhs, rhs)
        elif ctx.LOG_XOR():
            return LOG_AND(LOG_NEG(LOG_AND(LOG_NEG(lhs), LOG_NEG(rhs))), LOG_NEG(LOG_AND(lhs, rhs)))
        elif ctx.LOG_IMPL():
            return LOG_NEG(LOG_AND(lhs, LOG_NEG(rhs)))
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#SetExpr.
    def visitSetExpr(self, ctx:C2POParser.SetExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#RelExpr.
    def visitRelExpr(self, ctx:C2POParser.RelExprContext) -> EXPR:
        lineno: int = ctx.start.line
        lhs: LIT = self.visit(ctx.expr(0))
        rhs: LIT = self.visit(ctx.expr(1))

        if ctx.rel_eq_op():
            if ctx.rel_eq_op().REL_EQ():
                return REL_EQ(lhs, rhs)
            elif ctx.rel_eq_op().REL_NEQ:
                return REL_NEQ(lhs, rhs)
            else:
                raise RuntimeError
        elif ctx.rel_ineq_op():
            if ctx.rel_ineq_op().REL_GT():
                return REL_GT(lhs, rhs)
            elif ctx.rel_ineq_op().REL_LT():
                return REL_LT(lhs, rhs)
            elif ctx.rel_ineq_op().REL_GTE():
                return REL_GTE(lhs, rhs)
            elif ctx.rel_ineq_op().REL_LTE():
                return REL_LTE(lhs, rhs)
            else:
                raise RuntimeError
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#ArithMulExpr.
    def visitArithMulExpr(self, ctx:C2POParser.ArithMulExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ArithAddExpr.
    def visitArithAddExpr(self, ctx:C2POParser.ArithAddExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TLUnaryExpr.
    def visitTLUnaryExpr(self, ctx:C2POParser.TLUnaryExprContext):
        lineno: int = ctx.start.line
        operand: EXPR = self.visit(ctx.expr())
        bounds: Interval = self.visit(ctx.interval())

        if ctx.tl_unary_op():
            if ctx.tl_unary_op().TL_GLOBAL():
                return TL_GLOBAL(operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_FUTURE():
                return TL_UNTIL(BOOL(True), operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_HISTORICAL():
                return TL_HISTORICAL(operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_ONCE():
                return TL_ONCE(operand, bounds.lb, bounds.ub)
            else:
                raise RuntimeError
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#UnaryExpr.
    def visitUnaryExpr(self, ctx:C2POParser.UnaryExprContext) -> EXPR:
        lineno: int = ctx.start.line
        operand: EXPR = self.visit(ctx.expr())

        if ctx.unary_op().LOG_NEG():
            return LOG_NEG(operand)
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#FunExpr.
    def visitFunExpr(self, ctx:C2POParser.FunExprContext):
        # fun/filters
        # need way for user to define custom functions
        # need way for user to specify which functions are available
        # default configurations to choose from, also custom
        # e.g., no functions, only rel ops, rel ops and addition, etc.
        # each configuration will have its own canonical opcode definition

        print("Functions not implemented.")
        raise RuntimeError


    # Visit a parse tree produced by C2POParser#TernaryExpr.
    def visitTernaryExpr(self, ctx:C2POParser.TernaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#set_expr.
    def visitSet_expr(self, ctx:C2POParser.Set_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#interval.
    def visitInterval(self, ctx:C2POParser.IntervalContext) -> Interval:
        bounds = ctx.INT()

        if len(bounds) == 1:
            u: int = int(bounds[0].getText())
            return Interval(lb=0,ub=u)
        elif len(bounds) == 2:
            l: int = int(bounds[0].getText())
            u: int = int(bounds[1].getText())
            return Interval(lb=l,ub=u)
        else:
            raise RuntimeError


del C2POParser