# Generated from C2PO.g by ANTLR 4.10.1
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


    # Visit a parse tree produced by C2POParser#set_param.
    def visitSet_param(self, ctx:C2POParser.Set_paramContext):
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


    # Visit a parse tree produced by C2POParser#TermExpr.
    def visitTermExpr(self, ctx:C2POParser.TermExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TLBinExpr.
    def visitTLBinExpr(self, ctx:C2POParser.TLBinExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#LogBinExpr.
    def visitLogBinExpr(self, ctx:C2POParser.LogBinExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TLUnaryExpr.
    def visitTLUnaryExpr(self, ctx:C2POParser.TLUnaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#LogNegExpr.
    def visitLogNegExpr(self, ctx:C2POParser.LogNegExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ArithAddTerm.
    def visitArithAddTerm(self, ctx:C2POParser.ArithAddTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#TernaryTerm.
    def visitTernaryTerm(self, ctx:C2POParser.TernaryTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#UnaryTerm.
    def visitUnaryTerm(self, ctx:C2POParser.UnaryTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#BWBinTerm.
    def visitBWBinTerm(self, ctx:C2POParser.BWBinTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#SetTerm.
    def visitSetTerm(self, ctx:C2POParser.SetTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#RelTerm.
    def visitRelTerm(self, ctx:C2POParser.RelTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#LiteralTerm.
    def visitLiteralTerm(self, ctx:C2POParser.LiteralTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ArithMulTerm.
    def visitArithMulTerm(self, ctx:C2POParser.ArithMulTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#FuncTerm.
    def visitFuncTerm(self, ctx:C2POParser.FuncTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#ParensTerm.
    def visitParensTerm(self, ctx:C2POParser.ParensTermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#set_term.
    def visitSet_term(self, ctx:C2POParser.Set_termContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#interval.
    def visitInterval(self, ctx:C2POParser.IntervalContext):
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