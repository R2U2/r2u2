#type: ignore
from __future__ import annotations
from typing import Optional
from pathlib import Path

from c2po import sly, types, cpt, log

MODULE_CODE = "PRSC"

class C2POLexer(sly.Lexer):

    tokens = { KW_STRUCT, KW_INPUT, KW_DEFINE, KW_FTSPEC, KW_PTSPEC,
               KW_FOREACH, KW_FORSOME, KW_FOREXACTLY, KW_FORATLEAST, KW_FORATMOST,
               TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE, TL_UNTIL, TL_RELEASE, TL_SINCE, TL_TRIGGER, TL_MISSION_TIME, TL_TRUE, TL_FALSE,
               LOG_NEG, LOG_AND, LOG_OR, LOG_IMPL, LOG_IFF, LOG_XOR,
               BW_NEG, BW_AND, BW_OR, BW_XOR, BW_SHIFT_LEFT, BW_SHIFT_RIGHT,
               REL_EQ, REL_NEQ, REL_GTE, REL_LTE, REL_GT, REL_LT,
               ARITH_ADD, ARITH_SUB, ARITH_MUL, ARITH_DIV, ARITH_MOD, ARITH_POW, ARITH_SQRT, ARITH_ABS, RATE, #ARITH_PM,
               ASSIGN, CONTRACT_ASSIGN, SYMBOL, DECIMAL, NUMERAL, SEMI, COLON, DOT, DDOT, COMMA, #QUEST,
               LBRACK, RBRACK, LBRACE, RBRACE, LPAREN, RPAREN }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r"--.*"
    ignore_newline = r"\n+"

    REL_NEQ = r"!=|≠" # longer tokens must come first
    DECIMAL   = r"-?\d*\.\d+"
    NUMERAL     = r"-?[1-9][0-9]*|0"

    # Propositional logic ops/literals
    LOG_NEG  = r"!|¬"
    LOG_AND  = r"&&|∧"
    LOG_OR   = r"\|\||∨"
    LOG_IMPL = r"->|→"
    LOG_IFF  = r"<->|↔"

    # Bitwise ops
    BW_NEG          = r"~"
    BW_AND          = r"&" 
    BW_OR           = r"\|" 
    BW_XOR          = r"\^" 
    BW_SHIFT_LEFT   = r"<<"
    BW_SHIFT_RIGHT  = r">>"

    # Relational ops
    REL_EQ  = r"=="
    REL_GTE = r">=|≥"
    REL_LTE = r"<=|≤" 
    REL_GT  = r">"
    REL_LT  = r"<"

    # Arithmetic ops
    ARITH_ADD   = r"\+"
    ARITH_SUB   = r"-"
    ARITH_MUL   = r"\*|•|⋅"
    ARITH_DIV   = r"/|÷"
    ARITH_MOD   = r"%"
    # ARITH_PM    = r"\+/-|±"

    # Others
    RATE = r'rate'
    CONTRACT_ASSIGN = r"=>"
    ASSIGN  = r":="
    SYMBOL  = r"[a-zA-Z_][a-zA-Z0-9_]*"
    # QUEST   = r"\?"
    SEMI    = r";"
    COLON   = r":"
    DDOT     = r"\.\."
    DOT     = r"\."
    COMMA   = r","
    LBRACK  = r"\["
    RBRACK  = r"\]"
    LBRACE  = r"\{"
    RBRACE  = r"\}"
    LPAREN  = r"\("
    RPAREN  = r"\)"

    # Keywords
    SYMBOL["STRUCT"]     = KW_STRUCT
    SYMBOL["INPUT"]      = KW_INPUT
    SYMBOL["DEFINE"]     = KW_DEFINE
    SYMBOL["FTSPEC"]     = KW_FTSPEC
    SYMBOL["PTSPEC"]     = KW_PTSPEC
    SYMBOL["foreach"]    = KW_FOREACH
    SYMBOL["forsome"]    = KW_FORSOME
    SYMBOL["forexactly"] = KW_FOREXACTLY
    SYMBOL["foratleast"] = KW_FORATLEAST
    SYMBOL["foratmost"]  = KW_FORATMOST
    SYMBOL["pow"] = ARITH_POW
    SYMBOL["sqrt"] = ARITH_SQRT
    SYMBOL["abs"] = ARITH_ABS
    SYMBOL["xor"] = LOG_XOR
    SYMBOL['G'] = TL_GLOBAL
    SYMBOL['F'] = TL_FUTURE
    SYMBOL['H'] = TL_HIST
    SYMBOL['O'] = TL_ONCE
    SYMBOL['U'] = TL_UNTIL
    SYMBOL['R'] = TL_RELEASE
    SYMBOL['S'] = TL_SINCE
    SYMBOL['T'] = TL_TRIGGER
    SYMBOL['M'] = TL_MISSION_TIME
    SYMBOL["true"] = TL_TRUE
    SYMBOL["false"] = TL_FALSE

    def __init__(self, filename: str):
        super().__init__()
        self.filename = filename

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        log.error(MODULE_CODE, f"Illegal character '%s' {t.value[0]}", log.FileLocation(self.filename, self.lineno))
        self.index += 1


class C2POParser(sly.Parser):
    tokens = C2POLexer.tokens

    # Using C operator precedence as a guide
    precedence = (
        ("left", LOG_IMPL, LOG_XOR, LOG_IFF),
        ("left", LOG_OR),
        ("left", LOG_AND),
        ("left", TL_UNTIL, TL_RELEASE, TL_SINCE, TL_TRIGGER),
        ("left", BW_OR),
        ("left", BW_XOR),
        ("left", BW_AND),
        ("left", REL_EQ, REL_NEQ),
        ("left", REL_GT, REL_LT, REL_GTE, REL_LTE),
        ("left", BW_SHIFT_LEFT, BW_SHIFT_RIGHT),
        ("left", ARITH_ADD, ARITH_SUB),
        ("left", ARITH_MUL, ARITH_DIV, ARITH_MOD, ARITH_POW),
        ("right", LOG_NEG, BW_NEG, UNARY_ARITH_SUB, TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE),
        ("right", LPAREN, DOT, ARITH_SQRT, ARITH_ABS, RATE, LBRACK)
    )

    def __init__(self, filename: str, mission_time: int) :
        super().__init__()
        self.filename = filename
        self.mission_time = mission_time
        self.spec_num: int = 0
        self.literals = {}
        self.status = True

    def error(self, token):
        self.status = False
        lineno = getattr(token, "lineno", 0)
        if token:
            log.error(MODULE_CODE, f"Syntax error, unexpected token='{token.value}'", 
                      log.FileLocation(self.filename, lineno)
            )
        else:
            log.error(MODULE_CODE, f"Syntax error, token is 'None' (EOF)",
                      log.FileLocation(self.filename, lineno)
            )

    def fresh_label(self) -> str:
        return f"__f{self.spec_num}__"

    @_("section ft_spec_section")
    def section(self, p):
        return p[0] + [p[1]]

    @_("section pt_spec_section")
    def section(self, p):
        return p[0] + [p[1]]

    @_("section struct_section")
    def section(self, p):
        return p[0] + [p[1]]

    @_("section input_section")
    def section(self, p):
        return p[0] + [p[1]]

    @_("section define_section")
    def section(self, p):
        return p[0] + [p[1]]

    @_("")
    def section(self, p):
        return []

    @_("KW_STRUCT struct struct_list")
    def struct_section(self, p):
        return cpt.StructSection(log.FileLocation(self.filename, p.lineno), [p[1]] + p[2])

    @_("struct_list struct")
    def struct_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def struct_list(self, p):
        return []

    @_("SYMBOL COLON LBRACE variable_declaration_list RBRACE SEMI")
    def struct(self, p):
        members = []
        for typed_vars in p[3]:
            (ln, variables, type) = typed_vars
            member_decl = cpt.VariableDeclaration(ln, variables, type)
            members.append(member_decl)
            # (ln, variables, type) = typed_vars
            # for v in variables:
            #     members[v] = type

        return cpt.StructDefinition(log.FileLocation(self.filename, p.lineno), p[0], members)

    @_("KW_INPUT variable_declaration variable_declaration_list")
    def input_section(self, p):
        var_decl_list = [p[1]] + p[2]

        signal_declarations = []
        for typed_vars in var_decl_list:
            (ln, variables, type) = typed_vars
            signal_decl = cpt.VariableDeclaration(ln, variables, type)
            signal_declarations.append(signal_decl)

            if isinstance(type, types.ArrayType):
                continue

            for var in variables:
                self.literals[var] = cpt.Signal

        return cpt.InputSection(log.FileLocation(self.filename, p.lineno), signal_declarations)

    @_("variable_declaration_list variable_declaration")
    def variable_declaration_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def variable_declaration_list(self, p):
        return []

    @_("SYMBOL symbol_list COLON type SEMI")
    def variable_declaration(self, p):
        return (log.FileLocation(self.filename, p.lineno), [p[0]]+p[1], p[3])

    @_("symbol_list COMMA SYMBOL")
    def symbol_list(self, p):
        return p[0] + [p[2]]

    @_("")
    def symbol_list(self, p):
        return []

    # Non-parameterized type
    @_("SYMBOL")
    def type(self, p):
        if p[0] == "bool":
            return types.BoolType()
        elif p[0] == "int":
            return types.IntType()
        elif p[0] == "float":
            return types.FloatType()
        else:
            return types.StructType(p[0])
    
    # Array type
    @_("type LBRACK RBRACK")
    def type(self, p):
        return types.ArrayType(p[0])
    
    # Array type
    @_("type LBRACK NUMERAL RBRACK")
    def type(self, p):
        size = int(p[2])
        if size < 0:
            log.error(
                MODULE_CODE, 
                f"Array sizes must be greater than zero (found '{size}')", 
                log.FileLocation(self.filename, p.lineno)
            )
            self.status = False
        return types.ArrayType(p[0], size=size)

    @_("KW_DEFINE definition definition_list")
    def define_section(self, p):
        return cpt.DefineSection(log.FileLocation(self.filename, p.lineno), [p[1]] + p[2])

    @_("definition_list definition")
    def definition_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def definition_list(self, p):
        return []

    @_("SYMBOL ASSIGN expr SEMI")
    def definition(self, p):
        return cpt.Definition(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    # Future-time specification section
    @_("KW_FTSPEC spec spec_list")
    def ft_spec_section(self, p):
        return cpt.FutureTimeSpecSection(log.FileLocation(self.filename, p.lineno), [p[1]] + p[2])

    # Past-time specification section
    @_("KW_PTSPEC spec spec_list")
    def pt_spec_section(self, p):
        return cpt.PastTimeSpecSection(log.FileLocation(self.filename, p.lineno), [p[1]] + p[2])

    @_("spec_list spec")
    def spec_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def spec_list(self, p):
        return []

    # Basic specification
    @_("expr SEMI")
    def spec(self, p):
        formula = cpt.Formula(log.FileLocation(self.filename, p.lineno), self.fresh_label(), self.spec_num, p[0])
        self.spec_num += 1
        return formula

    # Labeled specification
    @_("SYMBOL COLON expr SEMI")
    def spec(self, p):
        if len(p[0]) > 50:
            log.error(
                MODULE_CODE, 
                f"Specification identifier name '{p[0]}' is too long, please chose a shorter name (limit 50 characters)", 
                log.FileLocation(self.filename, p.lineno)
            )
            self.status = False
        formula =  cpt.Formula(log.FileLocation(self.filename, p.lineno), p[0], self.spec_num, p[2])
        self.spec_num += 1
        return formula

    # Contract
    @_("SYMBOL COLON expr CONTRACT_ASSIGN expr SEMI")
    def spec(self, p):
        if len(p[0]) > 50:
            log.error(
                MODULE_CODE, 
                f"Specification identifier name '{p[0]}' is too long, please chose a shorter name (limit 50 characters)", 
                log.FileLocation(self.filename, p.lineno)
            )
            self.status = False
        contract = cpt.Contract(
            log.FileLocation(self.filename, p.lineno), 
            p[0], 
            self.spec_num, 
            self.spec_num+1, 
            self.spec_num+2, 
            p[2], 
            p[4]
        )
        self.spec_num += 3
        return contract

    @_("expr_list COMMA expr")
    def expr_list(self, p):
        p[0].append(p[2])
        return p[0]

    @_("")
    def expr_list(self, p):
        return []

    # Array expression
    @_("LBRACE expr expr_list RBRACE")
    def expr(self, p):
        return cpt.ArrayExpression(log.FileLocation(self.filename, p.lineno), [p[1]] + p[2])

    # Empty array expression
    @_("LBRACE RBRACE")
    def expr(self, p):
        return cpt.ArrayExpression(ln, [])

    # Parameterized set aggregation expression
    @_("KW_FOREXACTLY LPAREN SYMBOL COLON expr COMMA expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[2])
        return cpt.SetAggregation.ForExactly(log.FileLocation(self.filename, p.lineno), boundvar, p[4], p[6], p[9])

    @_("KW_FORATLEAST LPAREN SYMBOL COLON expr COMMA expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[2])
        return cpt.SetAggregation.ForAtLeast(log.FileLocation(self.filename, p.lineno), boundvar, p[4], p[6], p[9])

    @_("KW_FORATMOST LPAREN SYMBOL COLON expr COMMA expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[2])
        return cpt.SetAggregation.ForAtMost(log.FileLocation(self.filename, p.lineno), boundvar, p[4], p[6], p[9])

    # Set aggregation expression
    @_("KW_FOREACH LPAREN SYMBOL COLON expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[2])
        return cpt.SetAggregation.ForEach(log.FileLocation(self.filename, p.lineno), boundvar, p[4], p[7])

    @_("KW_FORSOME LPAREN SYMBOL COLON expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[2])
        return cpt.SetAggregation.ForSome(log.FileLocation(self.filename, p.lineno), boundvar, p[4], p[7])

    # Function/struct constructor expression nonempty arguments
    @_("SYMBOL LPAREN expr expr_list RPAREN")
    def expr(self, p):
        p[3].insert(0, p[2])
        return cpt.FunctionCall(log.FileLocation(self.filename, p.lineno), p[0], p[3])

    # Function/struct constructor expression empty arguments
    @_("SYMBOL LPAREN RPAREN")
    def expr(self, p):
        return cpt.FunctionCall(log.FileLocation(self.filename, p.lineno), p[0], [])

    # Struct member access
    @_("expr DOT SYMBOL")
    def expr(self, p):
        return cpt.StructAccess(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    # Array member access
    @_("expr LBRACK NUMERAL RBRACK")
    def expr(self, p):
        return cpt.ArrayIndex(log.FileLocation(self.filename, p.lineno), p[0], int(p[2]))
    
    # Array slice access
    @_("expr LBRACK NUMERAL DDOT NUMERAL RBRACK")
    def expr(self, p):
        return cpt.ArraySlice(log.FileLocation(self.filename, p.lineno), p[0], int(p[2]), int(p[4]))

    # Unary expressions
    @_("LOG_NEG expr")
    def expr(self, p):
        return cpt.Operator.LogicalNegate(log.FileLocation(self.filename, p.lineno), p[1])

    @_("BW_NEG expr")
    def expr(self, p):
        return cpt.Operator.BitwiseNegate(log.FileLocation(self.filename, p.lineno), p[1])

    @_("ARITH_SUB expr %prec UNARY_ARITH_SUB")
    def expr(self, p):
        return cpt.Operator.ArithmeticNegate(log.FileLocation(self.filename, p.lineno), p[1])
    
    @_("ARITH_SQRT LPAREN expr RPAREN")
    def expr(self, p):
        return cpt.Operator.ArithmeticSqrt(log.FileLocation(self.filename, p.lineno), p[2])
    
    @_("ARITH_ABS LPAREN expr RPAREN")
    def expr(self, p):
        return cpt.Operator.ArithmeticAbs(log.FileLocation(self.filename, p.lineno), p[2])
    
    @_("expr")
    def rate(self, p):
        return cpt.Operator.PreviousFunction(log.FileLocation(self.filename, p.lineno), p[0])

    @_("RATE LPAREN rate RPAREN")
    def expr(self, p):
        return cpt.Operator.RateFunction(log.FileLocation(self.filename, p.lineno), p[2].children[0], p[2])

    # Binary expressions
    @_("expr LOG_XOR expr")
    def expr(self, p):
        return cpt.Operator.LogicalXor(log.FileLocation(self.filename, p.lineno), [p[0], p[2]])
    
    @_("expr LOG_IMPL expr")
    def expr(self, p):
        return cpt.Operator.LogicalImplies(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr LOG_IFF expr")
    def expr(self, p):
        return cpt.Operator.LogicalIff(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr LOG_OR expr")
    def expr(self, p):
        return cpt.Operator.LogicalOr(log.FileLocation(self.filename, p.lineno), [p[0], p[2]])

    @_("expr LOG_AND expr")
    def expr(self, p):
        return cpt.Operator.LogicalAnd(log.FileLocation(self.filename, p.lineno), [p[0], p[2]])

    @_("expr BW_OR expr")
    def expr(self, p):
        return cpt.Operator.BitwiseOr(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr BW_XOR expr")
    def expr(self, p):
        return cpt.Operator.BitwiseXor(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr BW_AND expr")
    def expr(self, p):
        return cpt.Operator.BitwiseAnd(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr REL_EQ expr")
    def expr(self, p):
        return cpt.Operator.Equal(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr REL_NEQ expr")
    def expr(self, p):
        return cpt.Operator.NotEqual(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr REL_GT expr")
    def expr(self, p):
        return cpt.Operator.GreaterThan(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr REL_LT expr")
    def expr(self, p):
        return cpt.Operator.LessThan(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr REL_GTE expr")
    def expr(self, p):
        return cpt.Operator.GreaterThanOrEqual(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr REL_LTE expr")
    def expr(self, p):
        return cpt.Operator.LessThanOrEqual(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr BW_SHIFT_LEFT expr")
    def expr(self, p):
        return cpt.Operator.ShiftLeft(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr BW_SHIFT_RIGHT expr")
    def expr(self, p):
        return cpt.Operator.ShiftRight(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr ARITH_ADD expr")
    def expr(self, p):
        return cpt.Operator.ArithmeticAdd(log.FileLocation(self.filename, p.lineno), [p[0], p[2]])

    @_("expr ARITH_SUB expr")
    def expr(self, p):
        return cpt.Operator.ArithmeticSubtract(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr ARITH_MUL expr")
    def expr(self, p):
        return cpt.Operator.ArithmeticMultiply(log.FileLocation(self.filename, p.lineno), [p[0], p[2]])

    @_("expr ARITH_DIV expr")
    def expr(self, p):
        return cpt.Operator.ArithmeticDivide(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("expr ARITH_MOD expr")
    def expr(self, p):
        return cpt.Operator.ArithmeticModulo(log.FileLocation(self.filename, p.lineno), p[0], p[2])
    
    @_("expr ARITH_POW expr")
    def expr(self, p):
        return cpt.Operator.ArithmeticPower(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    # Unary temporal expressions
    @_("TL_GLOBAL interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Global(log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2])

    @_("TL_FUTURE interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Future(log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2])

    @_("TL_HIST interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Historical(log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2])

    @_("TL_ONCE interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Once(log.FileLocation(self.filename, p.lineno),  p[1].lb, p[1].ub, p[2])

    # Binary temporal expressions
    @_("expr TL_UNTIL interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Until(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])

    @_("expr TL_RELEASE interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Release(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])

    @_("expr TL_SINCE interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Since(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])
    
    @_("expr TL_TRIGGER interval expr")
    def expr(self, p):
        return cpt.TemporalOperator.Trigger(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])

    # Parentheses
    @_("LPAREN expr RPAREN")
    def expr(self, p):
        return p[1]

    # Symbol
    @_("TL_TRUE")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), True)

    # Symbol
    @_("TL_FALSE")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), False)

    # Symbol
    @_("SYMBOL")
    def expr(self, p):
        if p[0] in self.literals:
            if self.literals[p[0]] is cpt.Signal:
                return cpt.Signal(log.FileLocation(self.filename, p.lineno), p[0], types.NoType())
        return cpt.Variable(log.FileLocation(self.filename, p.lineno), p[0])

    # Integer
    @_("NUMERAL")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), int(p[0]))

    # Float
    @_("DECIMAL")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), float(p[0]))
        
    # Shorthand interval
    @_("LBRACK bound RBRACK")
    def interval(self, p):
        return types.Interval(0, p[1])

    # Standard interval
    @_("LBRACK bound COMMA bound RBRACK")
    def interval(self, p):
        return types.Interval(p[1], p[3])

    @_("NUMERAL")
    def bound(self, p):
        num = int(p[0])
        if int(p[0]) < 0:
            log.error(
                MODULE_CODE, 
                f"Interval bounds must be greater than zero (found '{num}')", 
                log.FileLocation(self.filename, p.lineno)
            )
            self.status = False
        return num

    @_("TL_MISSION_TIME")
    def bound(self, p):
        if self.mission_time < 0:
            log.error(MODULE_CODE, f"Mission time used but not set. Set using the '--mission-time' option.", log.FileLocation(self.filename, p.lineno))
            self.status = False
        return self.mission_time


def parse_c2po(input_path: Path, mission_time: int) -> Optional[cpt.Program]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    log.debug(MODULE_CODE, 1, f"Parsing {input_path}")

    with open(input_path, "r") as f:
        contents = f.read()

    lexer: C2POLexer = C2POLexer(input_path.name)
    parser: C2POParser = C2POParser(input_path.name, mission_time)
    sections: list[cpt.C2POSection] = parser.parse(lexer.tokenize(contents))

    if not parser.status:
        return None

    return cpt.Program(0, sections)

