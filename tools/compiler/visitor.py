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
        self.structs: dict[str,list[tuple[str,Type]]] = {}
        self.vars: dict[str,Type] = {}
        self.defs: dict[str,EXPR] = {}
        self.order: dict[str,int] = {}
        self.spec_num: int = 0
        self.status = True


    def error(self, msg) -> None:
        logger.error(msg)
        self.status = False

    
    def warning(self, msg) -> None:
        logger.warning(msg)


    # Visit a parse tree produced by C2POParser#start.
    def visitStart(self, ctx:C2POParser.StartContext) -> list[PROGRAM]:
        ln: int = ctx.start.line 

        for s in ctx.struct_block():
            self.visit(s)
        for v in ctx.var_block():
            self.visit(v)
        for d in ctx.def_block():
            self.visit(d)

        ret: list[PROGRAM] = []
        for s in ctx.spec_block():
            ret.append(self.visit(s))
        return ret


    # Visit a parse tree produced by C2POParser#struct_block.
    def visitStruct_block(self, ctx:C2POParser.Struct_blockContext):
        ln: int = ctx.start.line 

        s: STRUCT

        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#struct.
    def visitStruct(self, ctx:C2POParser.StructContext) -> None:
        ln: int = ctx.start.line 
        var_type: Type
        var_list: list[str]

        name: str = ctx.IDENTIFIER().getText()

        for vl in ctx.var_list():
            var_type, var_list = self.visit(vl)

        self.structs[name] = [var_type,var_list]
        


    # Visit a parse tree produced by C2POParser#var_block.
    def visitVar_block(self, ctx:C2POParser.Var_blockContext) -> None:
        ln: int = ctx.start.line
        var_type: Type
        var_list: list[str]

        for vl in ctx.var_list():
            var_type, var_list = self.visit(vl)
            for v in var_list:
                self.vars[v] = var_type


    # Visit a parse tree produced by C2POParser#var_list.
    def visitVar_list(self, ctx:C2POParser.Var_listContext) -> [Type,list[str]]:
        ln: int = ctx.start.line
        var_type: Type = self.visit(ctx.type_())

        id: TerminalNode
        var_list: list[str] = []
        for id in ctx.IDENTIFIER():
            var_list.append(id.getText())

        return [var_type,var_list]

    
    # Visit a parse tree produced by C2POParser#order_list.
    def visitOrder_list(self, ctx:C2POParser.Order_listContext) -> None:
        ln: int = ctx.start.line
        var_list: list[str] = list(self.vars)
        sid: int = 0
        id: TerminalNode

        for id in ctx.IDENTIFIER():
            if not id.getText() in var_list:
                sid += 1 # error? var in order but not declared
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
            return Bool()
        elif text == 'int':
            return Int()
        elif text == 'float':
            return Float()
        elif ctx.KW_SET:
            t: Type = self.visit(ctx.type_())
            return Set(t)

        self.error(f'{ln}: Type \'{text}\' not recognized')
        return NoType()


    # Visit a parse tree produced by C2POParser#def_block.
    def visitDef_block(self, ctx:C2POParser.Def_blockContext) -> None:
        ln: int = ctx.start.line
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#def.
    def visitDef(self, ctx:C2POParser.DefContext) -> None:
        ln: int = ctx.start.line
        var: str = ctx.IDENTIFIER().getText()
        expr: EXPR = self.visit(ctx.expr())

        if not var in self.vars.keys():
            self.error(f'{ln}: Variable \'{var}\' undeclared')
        elif var in list(self.order):
            self.warning(f'{ln}: Definition \'{var}\' used in Order statement, treating as signal and skipping')
        else:
            self.defs[var] = expr


    # Visit a parse tree produced by C2POParser#spec_block.
    def visitSpec_block(self, ctx:C2POParser.Spec_blockContext) -> PROGRAM:
        ln: int = ctx.start.line
        specs: list[SPEC]
        spec_dict: dict[int,SPEC] = {}
        contract_dict: dict[int,SPEC] = {}

        self.spec_num = 0

        for s in ctx.spec():
            specs = self.visit(s)

            if len(specs) > 1: # then s is a contract
                contract_dict[self.spec_num] = specs[0]

            for sp in specs:
                spec_dict[self.spec_num] = sp
                self.spec_num += 1

        return PROGRAM(ln, spec_dict, contract_dict, self.order)


    # Visit a parse tree produced by C2POParser#spec.
    def visitSpec(self, ctx:C2POParser.SpecContext) -> list[SPEC]:
        ln: int = ctx.start.line
        label: str = ''

        if ctx.expr():
            expr: EXPR = self.visit(ctx.expr())
        
            # if spec has a label, can be referred to in other specs
            # else, cannot be referred to later, do not store
            if ctx.IDENTIFIER(): 
                label = ctx.IDENTIFIER().getText()
                if label in list(self.defs):
                    self.warning(f'{ln}: Spec label identifier \'{label}\' previously declared, not storing')
                else:
                    self.defs[label] = expr

            return [SPEC(ln, label, self.spec_num, expr)]
        else:
            f1,f2,f3 = self.visit(ctx.contract())
            label = ctx.IDENTIFIER().getText()

            return [SPEC(ln, label, self.spec_num, f1),
                    SPEC(ln, label, self.spec_num+1, f2),
                    SPEC(ln, label, self.spec_num+2, f3)]

            


    # Visit a parse tree produced by C2POParser#contract.
    def visitContract(self, ctx:C2POParser.ContractContext) -> list[EXPR]:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        f1: EXPR = lhs
        f2: EXPR = LOG_IMPL(ln,lhs,rhs)
        f3: EXPR = LOG_AND(ln,lhs,rhs)

        return [f1,f2,f3]


    # Visit a parse tree produced by C2POParser#LogBinExpr.
    def visitLogBinExpr(self, ctx:C2POParser.LogBinExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.LOG_OR():
            return LOG_OR(ln, lhs, rhs)
        elif ctx.LOG_AND():
            return LOG_AND(ln, lhs, rhs)
        elif ctx.LOG_XOR():
            return LOG_XOR(ln, lhs, rhs)
        elif ctx.LOG_IMPL():
            return LOG_IMPL(ln, lhs, rhs)
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#TLBinExpr.
    def visitTLBinExpr(self, ctx:C2POParser.TLBinExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))
        bounds: Interval = self.visit(ctx.tl_bin_op().interval())

        if ctx.tl_bin_op():
            if ctx.tl_bin_op().TL_UNTIL():
                return TL_UNTIL(ln, lhs, rhs, bounds.lb, bounds.ub)
            elif ctx.tl_bin_op().TL_RELEASE():
                return TL_RELEASE(ln, lhs, rhs, bounds.lb, bounds.ub)
            elif ctx.tl_bin_op().TL_SINCE():
                return TL_SINCE(ln, lhs, rhs, bounds.lb, bounds.ub)
            else:
                self.error(f'{ln}: Binary TL op \'{ctx.tl_bin_op().start.text}\' not recognized')
                return EXPR(ln, [])
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#TLUnaryExpr.
    def visitTLUnaryExpr(self, ctx:C2POParser.TLUnaryExprContext) -> EXPR:
        ln: int = ctx.start.line
        operand: EXPR = self.visit(ctx.expr())
        bounds: Interval = self.visit(ctx.tl_unary_op().interval())

        if ctx.tl_unary_op():
            if ctx.tl_unary_op().TL_GLOBAL():
                return TL_GLOBAL(ln, operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_FUTURE():
                return TL_FUTURE(ln, operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_HISTORICAL():
                return TL_HISTORICAL(ln, operand, bounds.lb, bounds.ub)
            elif ctx.tl_unary_op().TL_ONCE():
                return TL_ONCE(ln, operand, bounds.lb, bounds.ub)
            else:
                self.error(f'{ln}: Unary TL op \'{ctx.tl_unary_op().start.text}\' not recognized')
                return EXPR(ln, [])
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext) -> EXPR:
        return self.visit(ctx.expr())


    # Visit a parse tree produced by C2POParser#TernaryExpr.
    def visitTernaryExpr(self, ctx:C2POParser.TernaryExprContext) -> EXPR:
        self.error(f'{ln}: Ternary operator not supported')
        return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#BWExpr.
    def visitBWExpr(self, ctx:C2POParser.BWExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.BW_OR():
            return BW_OR(ln, lhs, rhs)
        elif ctx.BW_XOR():
            return BW_XOR(ln, lhs, rhs)
        elif ctx.BW_AND():
            return BW_AND(ln, lhs, rhs)
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])
            

    # Visit a parse tree produced by C2POParser#RelExpr.
    def visitRelExpr(self, ctx:C2POParser.RelExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.rel_eq_op():
            if ctx.rel_eq_op().REL_EQ():
                return REL_EQ(ln, lhs, rhs)
            elif ctx.rel_eq_op().REL_NEQ:
                return REL_NEQ(ln, lhs, rhs)
            else:
                self.error(f'{ln}: Rel op \'{ctx.rel_eq_op().start.text}\' not recognized')
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
                self.error(f'{ln}: Rel op \'{ctx.rel_ineq_op().start.text}\' not recognized')
                return EXPR(ln, [])
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#ArithAddExpr.
    def visitArithAddExpr(self, ctx:C2POParser.ArithAddExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.arith_add_op():
            if ctx.arith_add_op().ARITH_ADD():
                return ARITH_ADD(ln, lhs, rhs)
            elif ctx.arith_add_op().ARITH_SUB():
                return ARITH_SUB(ln, lhs, rhs)
            else:
                self.error(f'{ln}: Unary TL op \'{ctx.tl_unary_op().start.text}\' not recognized')
                return EXPR(ln, [])
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#ArithMulExpr.
    def visitArithMulExpr(self, ctx:C2POParser.ArithMulExprContext) -> EXPR:
        ln: int = ctx.start.line
        lhs: EXPR = self.visit(ctx.expr(0))
        rhs: EXPR = self.visit(ctx.expr(1))

        if ctx.arith_mul_op():
            if ctx.arith_mul_op().ARITH_MUL():
                return ARITH_MUL(ln, lhs, rhs)
            elif ctx.arith_mul_op().ARITH_DIV():
                return ARITH_DIV(ln, lhs, rhs)
            elif ctx.arith_mul_op().ARITH_MOD():
                return ARITH_MOD(ln, lhs, rhs)
            else:
                self.error(f'{ln}: Binary arithmetic op \'{ctx.tl_bin_op().start.text}\' not recognized')
                return EXPR(ln, [])
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#UnaryExpr.
    def visitUnaryExpr(self, ctx:C2POParser.UnaryExprContext) -> EXPR:
        ln: int = ctx.start.line
        op: EXPR = self.visit(ctx.expr(0))

        if ctx.unary_op():
            if ctx.unary_op.ARITH_SUB():
                return ARITH_NEG(ln, op)
            elif ctx.unary_op.BW_NEG():
                return BW_NEG(ln, op)
            else:
                self.error(f'{ln}: Unary op \'{ctx.unary_op().start.text}\' not recognized')
                return EXPR(ln, [])
        else:
            self.error(f'{ln}: Expression not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#FuncExpr.
    def visitFuncExpr(self, ctx:C2POParser.FuncExprContext):
        ln: int = ctx.start.line
        self.error(f'{ln}: Functions not implemented')
        return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#StructMemberExpr.
    def visitStructMemberExpr(self, ctx:C2POParser.StructMemberExprContext):
        print(ctx.IDENTIFIER().getText())
        return self.visitChildren(ctx)


    # Visit a parse tree produced by C2POParser#SetExpr.
    def visitSetExpr(self, ctx:C2POParser.SetExprContext) -> EXPR:
        ln: int = ctx.start.line
        members: list[EXPR] = []
        
        if ctx.set_expr.expr_list():
            members = self.visit(ctx.set_expr.expr_list())

        return SET(ln, members)


    # Visit a parse tree produced by C2POParser#ParensExpr.
    def visitParensExpr(self, ctx:C2POParser.ParensExprContext) -> EXPR:
        return self.visit(ctx.expr())


    # Visit a parse tree produced by C2POParser#LiteralExpr.
    def visitLiteralExpr(self, ctx:C2POParser.LiteralExprContext) -> EXPR:
        ln: int = ctx.start.line

        literal: C2POParser.LiteralContext = ctx.literal()

        if literal.TRUE():
            return BOOL(ln, True)
        elif literal.FALSE():
            return BOOL(ln, False)
        elif literal.IDENTIFIER():
            name: str = literal.IDENTIFIER().getText()
            if name in self.defs.keys():
                return self.defs[name]
            elif name in self.order.keys():
                return SIGNAL(ln, name, self.vars[name])
            else:
                self.error(f'{ln}: Variable \'{name}\' undefined')
                return EXPR(ln, [])
        elif literal.INT():
            return INT(ln, int(literal.INT().getText()))
        elif literal.FLOAT():
            return FLOAT(ln, float(literal.FLOAT().getText()))
        else:
            self.error(f'{ln}: Literal \'{ctx.start.text}\' parser token not recognized')
            return EXPR(ln, [])


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
            self.error(f'{ln}: Expression not recognized')
            return Interval(0,0)


        # Visit a parse tree produced by C2POParser#expr_list.
    def visitExpr_list(self, ctx:C2POParser.Expr_listContext) -> list[EXPR]:
        ln: int = ctx.start.line
        exprs: list[EXPR] = []

        for expr in ctx.expr():
            e: EXPR = self.visit(expr)
            exprs.append(e)

        return exprs


del C2POParser