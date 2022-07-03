from logging import getLogger
from typing_extensions import get_overloads

from antlr4 import TerminalNode

from .parser.C2POVisitor import C2POVisitor
from .parser.C2POParser import C2POParser
from .ast import *
from .util import *

logger = getLogger(logger_name)

class Visitor(C2POVisitor):

    def __init__(self) -> None:
        super().__init__()
        self.vars: dict[str,Type] = {}
        self.defs: dict[str,EXPR] = {}
        self.order: dict[str,int] = {}
        self.spec_num: int = 0
        self.status = True


    # Visit a parse tree produced by C2POParser#start.
    def visitStart(self, ctx:C2POParser.StartContext) -> list[PROGRAM]:
        ln: int = ctx.start.line

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
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#var_list.
    def visitVar_list(self, ctx:C2POParser.Var_listContext) -> None:
        ln: int = ctx.start.line
        var_type: Type = self.visit(ctx.type_())

        id: TerminalNode
        for id in ctx.IDENTIFIER():
            self.vars[id.getText()] = var_type

    
    # Visit a parse tree produced by C2POParser#order_list.
    def visitOrder_list(self, ctx:C2POParser.Order_listContext) -> None:
        ln: int = ctx.start.line
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
        ln: int = ctx.start.line
        text = ctx.getText()

        if text == 'bool':
            return Type.BOOL
        elif text == 'int':
            return Type.INT
        elif text == 'float':
            return Type.FLOAT
        # elif ctx.KW_SET:
        #     return Type.SET

        logger.error('%d: Type \'%s\' not recognized', ln, text)
        return Type.NONE


    # Visit a parse tree produced by C2POParser#set_param.
    def visitSet_param(self, ctx:C2POParser.Set_paramContext) -> None:
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def_block.
    def visitDef_block(self, ctx:C2POParser.Def_blockContext) -> None:
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def.
    def visitDef(self, ctx:C2POParser.DefContext) -> None:
        ln: int = ctx.start.line
        var: str = ctx.IDENTIFIER().getText()
        expr: EXPR = self.visit(ctx.expr())

        if var in list(self.vars):
            logger.warning('%d: Definition \'%s\' declared in VAR, skipping', ln, var)
        else:
            self.defs[var] = expr


    # Visit a parse tree produced by C2POParser#spec_block.
    def visitSpec_block(self, ctx:C2POParser.Spec_blockContext) -> PROGRAM:
        ln: int = ctx.start.line
        spec: SPEC
        spec_dict: dict[int,SPEC] = {}

        self.spec_num = 0

        for s in ctx.spec():
            spec = self.visit(s)
            spec_dict[self.spec_num] = spec
            self.spec_num += 1

        return PROGRAM(ln, spec_dict,self.order)


    # Visit a parse tree produced by C2POParser#spec.
    def visitSpec(self, ctx:C2POParser.SpecContext) -> SPEC:
        ln: int = ctx.start.line
        expr: EXPR = self.visit(ctx.expr())
        label: str = ''

        # if spec has a label, can be referred to in other specs
        # else, cannot be referred to later, do not store
        if ctx.IDENTIFIER(): 
            label = ctx.IDENTIFIER().getText()
            if label in list(self.defs):
                logger.warning('%d: Spec label identifier \'%s\' previously declared, not storing', ln, label)
            else:
                self.defs[label] = expr

        return SPEC(ln, label, self.spec_num, expr)


    # Visit a parse tree produced by C2POParser#LitExpr.
    def visitLitExpr(self, ctx:C2POParser.LitExprContext) -> EXPR:
        ln: int = ctx.start.line

        if ctx.log_lit():
            return self.visit(ctx.log_lit())
        elif ctx.IDENTIFIER():
            name: str = ctx.IDENTIFIER().getText()
            if name in list(self.defs):
                return self.defs[name]
            elif name in list(self.vars):
                return VAR(ln, name, self.vars[name])
            else:
                logger.error('%d: Variable \'%s\' referenced but not declared', ln, name)
                return EXPR(ln, [])
        elif ctx.INT():
            return INT(ln, int(ctx.INT().getText()))
        elif ctx.FLOAT():
            return FLOAT(ln, float(ctx.FLOAT().getText()))
        else:
            logger.error('%d: Literal \'%s\' parser token not recognized', ln, ctx.start.text)
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#log_lit.
    def visitLog_lit(self, ctx:C2POParser.Log_litContext) -> EXPR:
        ln: int = ctx.start.line

        if ctx.TRUE():
            return BOOL(ln, True)
        elif ctx.FALSE():
            return BOOL(ln, False)
        else:
            logger.error('%d: Logical literal \'%s\' not recognized', ln, ctx.start.text)
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext) -> EXPR:
        ln: int = ctx.start.line
        return self.visit(ctx.expr())


    # Visit a parse tree produced by C2POParser#TLBinExpr.
    def visitTLBinExpr(self, ctx:C2POParser.TLBinExprContext):
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))
        bounds: Interval = self.visit(ctx.interval())

        if ctx.tl_bin_op():
            if ctx.tl_bin_op().TL_UNTIL():
                return TL_UNTIL(ln, lhs, rhs, bounds.lb, bounds.ub)
            elif ctx.tl_bin_op().TL_RELEASE():
                return LOG_NEG(ln, TL_RELEASE(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs), bounds.lb, bounds.ub))
            elif ctx.tl_bin_op().TL_SINCE():
                return TL_SINCE(ln, lhs, rhs, bounds.lb, bounds.ub)
            else:
                logger.error('%d: Binary TL op \'%s\' not recognized', ln, ctx.tl_bin_op().start.text)
                return EXPR(ln, [])
        else:
            logger.error('%d: Expression not recognized', ln)
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#LogBinExpr.
    def visitLogBinExpr(self, ctx:C2POParser.LogBinExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.LOG_OR():
            return LOG_NEG(ln, LOG_AND(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs)))
        elif ctx.LOG_AND():
            return LOG_AND(ln, lhs, rhs)
        elif ctx.LOG_XOR():
            return LOG_AND(ln, LOG_NEG(ln, LOG_AND(ln, LOG_NEG(ln, lhs), LOG_NEG(ln, rhs))), \
                                                    LOG_NEG(ln, LOG_AND(ln, lhs, rhs)))
        elif ctx.LOG_IMPL():
            return LOG_NEG(ln, LOG_AND(ln, lhs, LOG_NEG(ln, rhs)))
        else:
            logger.error('%d: Expression not recognized', ln)
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#SetExpr.
    def visitSetExpr(self, ctx:C2POParser.SetExprContext):
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#RelExpr.
    def visitRelExpr(self, ctx:C2POParser.RelExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: LIT = self.visit(ctx.expr(0))
        rhs: LIT = self.visit(ctx.expr(1))

        if ctx.rel_eq_op():
            if ctx.rel_eq_op().REL_EQ():
                return REL_EQ(ln, lhs, rhs)
            elif ctx.rel_eq_op().REL_NEQ:
                return REL_NEQ(ln, lhs, rhs)
            else:
                logger.error('%d: Rel op \'%s\' not recognized', ln, ctx.rel_eq_op().start.text)
                return EXPR(ln, [])
        elif ctx.rel_ineq_op():
            if ctx.rel_ineq_op().REL_GT():
                return REL_GT(ln, lhs, rhs)
            elif ctx.rel_ineq_op().REL_LT():
                return REL_LT(ln, lhs, rhs)
            elif ctx.rel_ineq_op().REL_GTE():
                return REL_GTE(ln, lhs, rhs)
            elif ctx.rel_ineq_op().REL_LTE():
                return REL_LTE(ln, lhs, rhs)
            else:
                logger.error('%d: Rel op \'%s\' not recognized', ln, ctx.rel_ineq_op().start.text)
                return EXPR(ln, [])
        else:
            logger.error('%d: Expression not recognized', ln)
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#ArithMulExpr.
    def visitArithMulExpr(self, ctx:C2POParser.ArithMulExprContext):
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ArithAddExpr.
    def visitArithAddExpr(self, ctx:C2POParser.ArithAddExprContext):
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TLUnaryExpr.
    def visitTLUnaryExpr(self, ctx:C2POParser.TLUnaryExprContext):
        ln: int = ctx.start.line
        operand: EXPR = self.visit(ctx.expr())
        bounds: Interval = self.visit(ctx.interval())

        if ctx.tl_unary_op():
            if ctx.tl_unary_op().TL_GLOBAL():
                return TL_GLOBAL(ln, operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_FUTURE():
                return TL_UNTIL(ln, BOOL(ln, True), operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_HISTORICAL():
                return TL_HISTORICAL(ln, operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_ONCE():
                return TL_ONCE(ln, operand, bounds.lb, bounds.ub)
            else:
                logger.error('%d: Unary TL op \'%s\' not recognized', ln, ctx.tl_unary_op().start.text)
                return EXPR(ln, [])
        else:
            logger.error('%d: Expression not recognized', ln)
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#UnaryExpr.
    def visitUnaryExpr(self, ctx:C2POParser.UnaryExprContext) -> EXPR:
        ln: int = ctx.start.line
        operand: EXPR = self.visit(ctx.expr())

        if ctx.unary_op().LOG_NEG():
            return LOG_NEG(ln, operand)
        else:
            logger.error('%d: Expression not recognized', ln)
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#FunExpr.
    def visitFunExpr(self, ctx:C2POParser.FunExprContext) -> EXPR:
        ln: int = ctx.start.line
        # fun/filters
        # need way for user to define custom functions
        # need way for user to specify which functions are available
        # default configurations to choose from, also custom
        # e.g., no functions, only rel ops, rel ops and addition, etc.
        # each configuration will have its own canonical opcode definition

        logger.error('%d: Functions not implemented', ln)
        return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#TernaryExpr.
    def visitTernaryExpr(self, ctx:C2POParser.TernaryExprContext):
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#set_expr.
    def visitSet_expr(self, ctx:C2POParser.Set_exprContext):
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


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
            logger.error('%d: Expression not recognized', ln)
            return Interval(0,0)


del C2POParser