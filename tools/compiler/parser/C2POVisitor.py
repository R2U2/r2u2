# Generated from C2PO.g by ANTLR 4.11.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .C2POParser import C2POParser
else:
    from C2POParser import C2POParser

# This class defines a complete generic visitor for a parse tree produced by C2POParser.

class C2POVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by C2POParser#start.
    def visitStart(self, ctx:C2POParser.StartContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#var_block.
    def visitVar_block(self, ctx:C2POParser.Var_blockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#var_list.
    def visitVar_list(self, ctx:C2POParser.Var_listContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#order_list.
    def visitOrder_list(self, ctx:C2POParser.Order_listContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#type.
    def visitType(self, ctx:C2POParser.TypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def_block.
    def visitDef_block(self, ctx:C2POParser.Def_blockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def.
    def visitDef(self, ctx:C2POParser.DefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#spec_block.
    def visitSpec_block(self, ctx:C2POParser.Spec_blockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#spec.
    def visitSpec(self, ctx:C2POParser.SpecContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#contract.
    def visitContract(self, ctx:C2POParser.ContractContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ArithAddExpr.
    def visitArithAddExpr(self, ctx:C2POParser.ArithAddExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#BWExpr.
    def visitBWExpr(self, ctx:C2POParser.BWExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TLBinExpr.
    def visitTLBinExpr(self, ctx:C2POParser.TLBinExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ArithMulExpr.
    def visitArithMulExpr(self, ctx:C2POParser.ArithMulExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#RelExpr.
    def visitRelExpr(self, ctx:C2POParser.RelExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#FuncExpr.
    def visitFuncExpr(self, ctx:C2POParser.FuncExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#UnaryExpr.
    def visitUnaryExpr(self, ctx:C2POParser.UnaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TLUnaryExpr.
    def visitTLUnaryExpr(self, ctx:C2POParser.TLUnaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#LogBinExpr.
    def visitLogBinExpr(self, ctx:C2POParser.LogBinExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#SetExpr.
    def visitSetExpr(self, ctx:C2POParser.SetExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#LiteralExpr.
    def visitLiteralExpr(self, ctx:C2POParser.LiteralExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TernaryExpr.
    def visitTernaryExpr(self, ctx:C2POParser.TernaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#set_expr.
    def visitSet_expr(self, ctx:C2POParser.Set_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#interval.
    def visitInterval(self, ctx:C2POParser.IntervalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#expr_list.
    def visitExpr_list(self, ctx:C2POParser.Expr_listContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#tl_unary_op.
    def visitTl_unary_op(self, ctx:C2POParser.Tl_unary_opContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#tl_bin_op.
    def visitTl_bin_op(self, ctx:C2POParser.Tl_bin_opContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#literal.
    def visitLiteral(self, ctx:C2POParser.LiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#rel_eq_op.
    def visitRel_eq_op(self, ctx:C2POParser.Rel_eq_opContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#rel_ineq_op.
    def visitRel_ineq_op(self, ctx:C2POParser.Rel_ineq_opContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#arith_add_op.
    def visitArith_add_op(self, ctx:C2POParser.Arith_add_opContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#arith_mul_op.
    def visitArith_mul_op(self, ctx:C2POParser.Arith_mul_opContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#unary_op.
    def visitUnary_op(self, ctx:C2POParser.Unary_opContext):
        return self.visitChildren(ctx)



del C2POParser