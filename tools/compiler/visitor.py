from antlr4 import TerminalNode

from .parser.C2POVisitor import C2POVisitor
from .parser.C2POParser import C2POParser

from .ast import *

class Visitor(C2POVisitor):
    vars: dict[str,Type] = {}
    # var_order: dict[Var,int]
    prog: PROGRAM

    # Visit a parse tree produced by C2POParser#start.
    def visitStart(self, ctx:C2POParser.StartContext) -> None:
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#block.
    def visitBlock(self, ctx:C2POParser.BlockContext) -> None:
        return self.visitChildren(ctx)


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
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#type.
    def visitType(self, ctx:C2POParser.TypeContext) -> Type:
        text = ctx.getText()

        if text == 'bool':
            return Type._BOOL
        elif text == 'int':
            return Type._INT
        elif text == 'float':
            return Type._FLOAT
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
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#spec_block.
    def visitSpec_block(self, ctx:C2POParser.Spec_blockContext) -> None:
        spec: SPEC
        spec_label: str
        spec_num: int = 0
        spec_dict: dict[tuple[int,str],SPEC] = {}

        for s in ctx.spec():
            spec = self.visit(s)

            if s.IDENTIFIER():
                spec_label = s.IDENTIFIER().getText()
            else:
                spec_label = ""

            spec_dict[(spec_num, spec_label)] = spec
            spec_num += 1

        self.prog = PROGRAM(1, self.vars, spec_dict)


    # Visit a parse tree produced by C2POParser#spec.
    def visitSpec(self, ctx:C2POParser.SpecContext) -> SPEC:
        return self.visit(ctx.expr())


    # Visit a parse tree produced by C2POParser#LitExpr.
    def visitLitExpr(self, ctx:C2POParser.LitExprContext) -> EXPR:
        lineno: int = ctx.start.line

        if ctx.log_lit():
            return ctx.log_lit().visit()
        elif ctx.IDENTIFIER():
            name: str = ctx.IDENTIFIER().getText()
            return VAR(lineno, self.vars[name], name)
        elif ctx.INT():
            # TODO handle possible exception
            return INT(lineno, Type._INT, int(ctx.INT().getText()))
        elif ctx.FLOAT():
            # TODO handle possible exception
            return FLOAT(lineno, Type._FLOAT, int(ctx.FLOAT().getText()))
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#log_lit.
    def visitLog_lit(self, ctx:C2POParser.Log_litContext) -> EXPR:
        lineno: int = ctx.start.line

        if ctx.TRUE():
            return BOOL(lineno, Type._BOOL, True)
        elif ctx.FALSE():
            return BOOL(lineno, Type._BOOL, False)
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
        bounds: tuple[int,int] = self.visit(ctx.interval())

        if ctx.tl_bin_op():
            if ctx.tl_bin_op().TL_UNTIL():
                return TL_UNTIL(lineno, Type._NONE, lhs, rhs, bounds)
            elif ctx.tl_bin_op().TL_RELEASE():
                return TL_RELEASE(lineno, Type._NONE, lhs, rhs, bounds)
            elif ctx.tl_bin_op().TL_SINCE():
                return TL_SINCE(lineno, Type._NONE, lhs, rhs, bounds)
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
            return LOG_OR(lineno, Type._NONE, lhs, rhs)
        elif ctx.LOG_AND():
            return LOG_AND(lineno, Type._NONE, lhs, rhs)
        elif ctx.LOG_XOR():
            return LOG_AND(lineno, Type._NONE, LOG_OR(lineno, Type._NONE, lhs, rhs), 
                                               LOG_NEG(lineno, Type._NONE, LOG_AND(lineno, Type._NONE, rhs,lhs)))
        elif ctx.LOG_IMPL():
            return LOG_OR(lineno, Type._NONE, LOG_NEG(lineno, Type._NONE, lhs), rhs)
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#SetExpr.
    def visitSetExpr(self, ctx:C2POParser.SetExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#RelExpr.
    def visitRelExpr(self, ctx:C2POParser.RelExprContext) -> EXPR:
        lineno: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.rel_eq_op():
            if ctx.rel_eq_op().REL_EQ():
                return REL_EQ(lineno, Type._NONE, lhs, rhs)
            elif ctx.rel_eq_op().REL_NEQ:
                return REL_NEQ(lineno, Type._NONE, lhs, rhs)
            else:
                raise RuntimeError
        elif ctx.rel_ineq_op():
            if ctx.rel_ineq_op().REL_GT():
                return REL_GT(lineno, Type._NONE, lhs, rhs)
            elif ctx.rel_ineq_op().REL_LT():
                return REL_LT(lineno, Type._NONE, lhs, rhs)
            elif ctx.rel_ineq_op().REL_GTE():
                return REL_GTE(lineno, Type._NONE, lhs, rhs)
            elif ctx.rel_ineq_op().REL_LTE():
                return REL_LTE(lineno, Type._NONE, lhs, rhs)
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
        bounds: tuple[int,int] = self.visit(ctx.interval())

        if ctx.tl_unary_op():
            if ctx.tl_unary_op().TL_GLOBAL():
                return TL_GLOBAL(lineno, Type._NONE, operand, bounds)
            elif ctx.tl_unary_op().TL_FUTURE():
                return TL_FUTURE(lineno, Type._NONE, operand, bounds)
            elif ctx.tl_unary_op().TL_HISTORICAL():
                return TL_HISTORICAL(lineno, Type._NONE, operand, bounds)
            elif ctx.tl_unary_op().TL_ONCE():
                return TL_ONCE(lineno, Type._NONE, operand, bounds)
            else:
                raise RuntimeError
        else:
            raise RuntimeError


    # Visit a parse tree produced by C2POParser#UnaryExpr.
    def visitUnaryExpr(self, ctx:C2POParser.UnaryExprContext) -> EXPR:
        lineno: int = ctx.start.line
        operand: EXPR = self.visit(ctx.expr())

        if ctx.unary_op():
            if ctx.unary_op().LOG_NEG():
                return LOG_NEG(lineno, Type._NONE, operand)
            elif ctx.unary_op().ARITH_NEG():
                return ARITH_NEG(lineno, Type._NONE, operand)
            else:
                raise RuntimeError
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
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TernaryExpr.
    def visitTernaryExpr(self, ctx:C2POParser.TernaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#set_expr.
    def visitSet_expr(self, ctx:C2POParser.Set_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#interval.
    def visitInterval(self, ctx:C2POParser.IntervalContext) -> tuple[int,int]:
        bounds = ctx.INT()

        if len(bounds) == 1:
            u: int = int(bounds[0].getText())
            return (0,u)
        elif len(bounds) == 2:
            l: int = int(bounds[0].getText())
            u: int = int(bounds[1].getText())
            return (l,u)
        else:
            raise RuntimeError


del C2POParser