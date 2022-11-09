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
        # self.structs: dict[str,tuple[list[str],list[Type]]] = {}
        self.structs: StructDict = {}
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
        for v in ctx.input_block():
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

        for s in ctx.struct():
            self.visit(s)


    # Visit a parse tree produced by C2POParser#struct.
    def visitStruct(self, ctx:C2POParser.StructContext) -> None:
        ln: int = ctx.start.line 

        id: str = ctx.IDENTIFIER().getText()
        for i in self.structs.keys():
            self.warning(f'{ln}: Struct {i} already defined, redefining')

        self.structs[id] = {}
        var_dict: dict[str,Type] = {}
        for vl in ctx.var_list():
            var_dict = self.visit(vl)
            self.structs[id].update(var_dict)
            # for i,t in var_dict.items():
            #     self.structs[id][0].append(i)
            #     self.structs[id][1].append(t)


    # Visit a parse tree produced by C2POParser#input_block.
    def visitInput_block(self, ctx:C2POParser.Input_blockContext):
        ln: int = ctx.start.line

        var_dict: dict[str,Type]
        for vl in ctx.var_list():
            var_dict = self.visit(vl)

            for id in var_dict.keys():
                if id in self.vars.keys():
                    self.warning(f'{ln}: Variable {id} declared more than once, using type {var_dict[id]}')

            self.vars.update(var_dict)

        if ctx.order_list():
            self.visit(ctx.order_list())


    # Visit a parse tree produced by C2POParser#var_list.
    def visitVar_list(self, ctx:C2POParser.Var_listContext) -> dict[str,Type]:
        ln: int = ctx.start.line
        var_type: Type = self.visit(ctx.type_())

        id: TerminalNode
        var_dict: dict[str,Type] = {}
        for id in ctx.IDENTIFIER():
            var_dict[id.getText()] = var_type

        return var_dict

    
    # Visit a parse tree produced by C2POParser#order_list.
    def visitOrder_list(self, ctx:C2POParser.Order_listContext) -> None:
        ln: int = ctx.start.line
        sid: int = 0
        id: TerminalNode

        for id in ctx.IDENTIFIER():
            if not id.getText() in self.vars.keys():
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
        elif ctx.KW_SET():
            t: Type = self.visit(ctx.type_())
            return Set(t)
        elif text in self.structs.keys():
            return Struct(text)

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

        if var in self.vars.keys():
            self.error(f'{ln}: Variable \'{var}\' already declared')
        elif var in self.defs.keys():
            self.warning(f'{ln}: Variable \'{var}\' defined twice, using most recent definition')
            self.defs[var] = expr
        # elif var in list(self.order):
        #     self.warning(f'{ln}: Definition \'{var}\' used in Order statement, treating as signal and skipping')
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

        return PROGRAM(ln, self.structs, spec_dict, contract_dict, self.order)


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
            return LOG_BIN_OR(ln, lhs, rhs)
        elif ctx.LOG_AND():
            return LOG_BIN_AND(ln, lhs, rhs)
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
    def visitFuncExpr(self, ctx:C2POParser.FuncExprContext) -> EXPR:
        ln: int = ctx.start.line
        id: str = ctx.IDENTIFIER().getText()
        elist: list[EXPR] = self.visit(ctx.expr_list())

        if id in self.structs.keys():
            members: dict[str,EXPR] = {}
            if len(elist) == len(self.structs[id]):
                for s in self.structs[id].keys():
                    members[s] = elist.pop(0)
                return STRUCT(ln,id,members)
            else:
                self.error(f'{ln}: Member mismatch for struct {id}, number of members do not match')
                return EXPR(ln, [])
        else:
            self.error(f'{ln}: Symbol {id} not recognized')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#SetAggExpr.
    def visitSetAggExpr(self, ctx:C2POParser.SetAggExprContext) -> EXPR:
        ln: int = ctx.start.line
        op: str = ctx.IDENTIFIER().getText()

        if op == 'allof':
            S,v = self.visit(ctx.set_agg_binder())
            self.defs[v.name] = v
            e: EXPR = self.visit(ctx.expr())
            del self.defs[v.name]
            return ALL_OF(ln,S,v,e)
        else:
            self.error(f'{ln}: Set aggregation operator {op} not supported')
            return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#set_agg_binder.
    def visitSet_agg_binder(self, ctx:C2POParser.Set_agg_binderContext) -> tuple[EXPR,VAR]:
        ln: int = ctx.start.line
        S: EXPR = self.visit(ctx.expr())
        v: VAR = VAR(ln,ctx.IDENTIFIER().getText())
        return (S,v)


    # Visit a parse tree produced by C2POParser#StructMemberExpr.
    def visitStructMemberExpr(self, ctx:C2POParser.StructMemberExprContext) -> EXPR:
        ln: int = ctx.start.line
        id: str = ctx.IDENTIFIER().getText()
        e: EXPR = self.visit(ctx.expr())

        return STRUCT_ACCESS(ln,e,id)

        # if isinstance(e,STRUCT):
        #     if id in e.members.keys():
        #         return e.members[id]
        #     else:
        #         self.error(f'{ln}: Member {id} of struct {e} does not exist')
        #         return EXPR(ln, [])
        # else:
        #     self.error(f'{ln}: Accessing member {id} of non-struct expression {e}')
        #     return EXPR(ln, [])


    # Visit a parse tree produced by C2POParser#SetExpr.
    def visitSetExpr(self, ctx:C2POParser.SetExprContext) -> EXPR:
        ln: int = ctx.start.line
        elements: list[EXPR] = []
        
        if ctx.set_expr().expr_list():
            elements = self.visit(ctx.set_expr().expr_list())

        return SET(ln, elements)


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