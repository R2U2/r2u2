#type: ignore
from signal import signal
from typing import Optional
from pathlib import Path

from .sly import Lexer, Parser
from .ast import *
from .logger import logger

class C2POLexer(Lexer):

    tokens = { KW_STRUCT, KW_INPUT, KW_DEFINE, KW_ATOMIC, KW_FTSPEC, KW_PTSPEC,
               KW_FOREACH, KW_FORSOME, KW_FOREXACTLY, KW_FORATLEAST, KW_FORATMOST,
               TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE, TL_UNTIL, TL_RELEASE, TL_SINCE, TL_MISSION_TIME, TL_TRUE, TL_FALSE,
               LOG_NEG, LOG_AND, LOG_OR, LOG_IMPL, LOG_IFF, #LOG_XOR,
               BW_NEG, BW_AND, BW_OR, BW_XOR, BW_SHIFT_LEFT, BW_SHIFT_RIGHT,
               REL_EQ, REL_NEQ, REL_GTE, REL_LTE, REL_GT, REL_LT,
               ARITH_ADD, ARITH_SUB, ARITH_MUL, ARITH_DIV, ARITH_MOD, #ARITH_POW, ARITH_SQRT, ARITH_PM,
               ASSIGN, CONTRACT_ASSIGN, SYMBOL, DECIMAL, NUMERAL, SEMI, COLON, DOT, COMMA, #QUEST,
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
    # LOG_XOR  = r"XOR|⊕"
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
    # ARITH_POW   = r"\*\*"
    # ARITH_SQRT  = r"√"
    # ARITH_PM    = r"\+/-|±"

    # Others
    CONTRACT_ASSIGN = r"=>"
    ASSIGN  = r":="
    SYMBOL  = r"[a-zA-Z_][a-zA-Z0-9_]*"
    # QUEST   = r"\?"
    SEMI    = r";"
    COLON   = r":"
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
    SYMBOL["ATOMIC"]     = KW_ATOMIC
    SYMBOL["FTSPEC"]     = KW_FTSPEC
    SYMBOL["PTSPEC"]     = KW_PTSPEC
    SYMBOL["foreach"]    = KW_FOREACH
    SYMBOL["forsome"]    = KW_FORSOME
    SYMBOL["forexactly"] = KW_FOREXACTLY
    SYMBOL["foratleast"] = KW_FORATLEAST
    SYMBOL["foratmost"]  = KW_FORATMOST
    SYMBOL['G'] = TL_GLOBAL
    SYMBOL['F'] = TL_FUTURE
    SYMBOL['H'] = TL_HIST
    SYMBOL['O'] = TL_ONCE
    SYMBOL['U'] = TL_UNTIL
    SYMBOL['R'] = TL_RELEASE
    SYMBOL['S'] = TL_SINCE
    SYMBOL['M'] = TL_MISSION_TIME
    SYMBOL["true"] = TL_TRUE
    SYMBOL["false"] = TL_FALSE

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        logger.error(f"{self.lineno}: Illegal character '%s' {t.value[0]}")
        self.index += 1


class C2POParser(Parser):
    tokens = C2POLexer.tokens

    # Using C operator precedence as a guide
    precedence = (
        ("left", LOG_IMPL, LOG_IFF),
        ("left", LOG_OR),
        ("left", LOG_AND),
        ("left", TL_UNTIL, TL_RELEASE, TL_SINCE),
        ("left", BW_OR),
        ("left", BW_XOR),
        ("left", BW_AND),
        ("left", REL_EQ, REL_NEQ),
        ("left", REL_GT, REL_LT, REL_GTE, REL_LTE),
        ("left", BW_SHIFT_LEFT, BW_SHIFT_RIGHT),
        ("left", ARITH_ADD, ARITH_SUB),
        ("left", ARITH_MUL, ARITH_DIV, ARITH_MOD),
        ("right", LOG_NEG, BW_NEG, UNARY_ARITH_SUB, TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE),
        ("right", LPAREN, DOT)
    )

    def __init__(self, mt: int) :
        super().__init__()
        self.mission_time = mt
        self.spec_num: int = 0
        self.literals = {}
        self.status = True

    def error(self, token):
        self.status = False
        lineno = getattr(token, "lineno", 0)
        logger.error(f"{lineno}: Syntax error, token='{token.value}'")

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

    @_("section atomic_section")
    def section(self, p):
        return p[0] + [p[1]]

    @_("")
    def section(self, p):
        return []

    @_("KW_STRUCT struct struct_list")
    def struct_section(self, p):
        return C2POStructSection(p.lineno, [p[1]] + p[2])

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
            member_decl = C2POVariableDeclaration(ln, variables, type)
            members.append(member_decl)
            # (ln, variables, type) = typed_vars
            # for v in variables:
            #     members[v] = type

        return C2POStructDefinition(p.lineno, p[0], members)

    @_("KW_INPUT variable_declaration variable_declaration_list")
    def input_section(self, p):
        var_decl_list = [p[1]] + p[2]

        signal_declarations = []
        for typed_vars in var_decl_list:
            (ln, variables, type) = typed_vars
            signal_decl = C2POVariableDeclaration(ln, variables, type)
            signal_declarations.append(signal_decl)

            for var in variables:
                self.literals[var] = C2POSignal

        return C2POInputSection(p.lineno, signal_declarations)

    @_("variable_declaration_list variable_declaration")
    def variable_declaration_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def variable_declaration_list(self, p):
        return []

    @_("SYMBOL symbol_list COLON type SEMI")
    def variable_declaration(self, p):
        return (p.lineno, [p[0]]+p[1], p[3])

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
            return C2POBoolType(False)
        elif p[0] == "int":
            return C2POIntType(False)
        elif p[0] == "float":
            return C2POFloatType(False)
        else:
            return C2POStructType(False, p[0])
    
    # Parameterized type
    @_("SYMBOL REL_LT type REL_GT")
    def type(self, p):
        if p[0] == "set":
            return C2POSetType(False, p[2])

        logger.error(f"{p.lineno}: Type \"{p[0]}\" not recognized")
        self.status = False
        return C2PONoType()

    @_("KW_DEFINE definition definition_list")
    def define_section(self, p):
        return C2PODefineSection(p.lineno, [p[1]] + p[2])

    @_("definition_list definition")
    def definition_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def definition_list(self, p):
        return []

    @_("SYMBOL ASSIGN expr SEMI")
    def definition(self, p):
        return C2PODefinition(p.lineno, p[0], p[2])

    @_("KW_ATOMIC atomic atomic_list")
    def atomic_section(self, p):
        p[2].append(p[1])
        self.literals[p[1].symbol] = C2POAtomicChecker
        return C2POAtomicSection(p.lineno, p[2])

    @_("atomic_list atomic")
    def atomic_list(self, p):
        self.literals[p[1].symbol] = C2POAtomicChecker
        return p[0] + [p[1]]

    @_("")
    def atomic_list(self, p):
        return []

    @_("SYMBOL ASSIGN expr SEMI")
    def atomic(self, p):
        return C2POAtomicCheckerDefinition(p.lineno, p[0], p[2])

    # Future-time specification section
    @_("KW_FTSPEC spec spec_list")
    def ft_spec_section(self, p):
        return C2POFutureTimeSpecSection(p.lineno, [p[1]] + p[2])

    # Past-time specification section
    @_("KW_PTSPEC spec spec_list")
    def pt_spec_section(self, p):
        return C2POPastTimeSpecSection(p.lineno, [p[1]] + p[2])

    @_("spec_list spec")
    def spec_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def spec_list(self, p):
        return []

    # Basic specification
    @_("expr SEMI")
    def spec(self, p):
        self.spec_num += 1
        return C2POSpecification(p.lineno, "", self.spec_num-1, p[0])

    # Labeled specification
    @_("SYMBOL COLON expr SEMI")
    def spec(self, p):
        self.spec_num += 1
        return C2POSpecification(p.lineno, p[0], self.spec_num-1, p[2])

    # Contract
    @_("SYMBOL COLON expr CONTRACT_ASSIGN expr SEMI")
    def spec(self, p):
        self.spec_num += 3
        return C2POContract(
            p.lineno, 
            p[0], 
            self.spec_num-3, 
            self.spec_num-2, 
            self.spec_num-1, 
            p[2], 
            p[4]
        )

    @_("expr_list COMMA expr")
    def expr_list(self, p):
        p[0].append(p[2])
        return p[0]

    @_("")
    def expr_list(self, p):
        return []

    # Set expression
    @_("LBRACE expr expr_list RBRACE")
    def expr(self, p):
        return C2POSet(p.lineno, [p[1]] + p[2])

    # Empty set expression
    @_("LBRACE RBRACE")
    def expr(self, p):
        return C2POSet(ln, [])

    # Parameterized set aggregation expression
    @_("KW_FOREXACTLY LPAREN SYMBOL COLON expr COMMA expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = C2POVariable(p.lineno, p[2])
        return C2POForExactly(p.lineno, p[4], p[6], boundvar, p[9])

    @_("KW_FORATLEAST LPAREN SYMBOL COLON expr COMMA expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = C2POVariable(p.lineno, p[2])
        return C2POForAtLeast(p.lineno, p[4], p[6], boundvar, p[9])

    @_("KW_FORATMOST LPAREN SYMBOL COLON expr COMMA expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = C2POVariable(p.lineno, p[2])
        return C2POForAtMost(p.lineno, p[4], p[6], boundvar, p[9])

    # Set aggregation expression
    @_("KW_FOREACH LPAREN SYMBOL COLON expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = C2POVariable(p.lineno, p[2])
        return C2POForEach(p.lineno, p[4], boundvar, p[7])

    @_("KW_FORSOME LPAREN SYMBOL COLON expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        boundvar = C2POVariable(p.lineno, p[2])
        return C2POForSome(p.lineno,  p[4], boundvar, p[7])

    # Function/struct constructor expression nonempty arguments
    @_("SYMBOL LPAREN expr expr_list RPAREN")
    def expr(self, p):
        p[3].append(p[2])
        p[3].reverse()
        return C2POFunctionCall(p.lineno, p[0], p[3])

    # Function/struct constructor expression empty arguments
    @_("SYMBOL LPAREN RPAREN")
    def expr(self, p):
        return C2POFunctionCall(p.lineno, p[0], [])

    # Struct member access
    @_("expr DOT SYMBOL")
    def expr(self, p):
        return C2POStructAccess(p.lineno, p[0], p[2])

    # Unary expressions
    @_("LOG_NEG expr")
    def expr(self, p):
        return C2POLogicalNegate(p.lineno, p[1])

    @_("BW_NEG expr")
    def expr(self, p):
        return C2POBitwiseNegate(p.lineno, p[1])

    @_("ARITH_SUB expr %prec UNARY_ARITH_SUB")
    def expr(self, p):
        return C2POArithmeticNegate(p.lineno, p[1])

    # Binary expressions
    @_("expr LOG_IMPL expr")
    def expr(self, p):
        return C2POLogicalImplies(p.lineno, p[0], p[2])

    @_("expr LOG_IFF expr")
    def expr(self, p):
        return C2POLogicalIff(p.lineno, p[0], p[2])

    @_("expr LOG_OR expr")
    def expr(self, p):
        return C2POLogicalOr(p.lineno, [p[0], p[2]])

    @_("expr LOG_AND expr")
    def expr(self, p):
        return C2POLogicalAnd(p.lineno, [p[0], p[2]])

    @_("expr BW_OR expr")
    def expr(self, p):
        return C2POBitwiseOr(p.lineno, p[0], p[2])

    @_("expr BW_XOR expr")
    def expr(self, p):
        return C2POBitwiseXor(p.lineno, p[0], p[2])

    @_("expr BW_AND expr")
    def expr(self, p):
        return C2POBitwiseAnd(p.lineno, p[0], p[2])

    @_("expr REL_EQ expr")
    def expr(self, p):
        return C2POEqual(p.lineno, p[0], p[2])

    @_("expr REL_NEQ expr")
    def expr(self, p):
        return C2PONotEqual(p.lineno, p[0], p[2])

    @_("expr REL_GT expr")
    def expr(self, p):
        return C2POGreaterThan(p.lineno, p[0], p[2])

    @_("expr REL_LT expr")
    def expr(self, p):
        return C2POLessThan(p.lineno, p[0], p[2])

    @_("expr REL_GTE expr")
    def expr(self, p):
        return C2POGreaterThanOrEqual(p.lineno, p[0], p[2])

    @_("expr REL_LTE expr")
    def expr(self, p):
        return C2POLessThanOrEqual(p.lineno, p[0], p[2])

    @_("expr BW_SHIFT_LEFT expr")
    def expr(self, p):
        return C2POBitwiseShiftLeft(p.lineno, p[0], p[2])

    @_("expr BW_SHIFT_RIGHT expr")
    def expr(self, p):
        return C2POBitwiseShiftRight(p.lineno, p[0], p[2])

    @_("expr ARITH_ADD expr")
    def expr(self, p):
        return C2POArithmeticAdd(p.lineno, p[0], p[2])

    @_("expr ARITH_SUB expr")
    def expr(self, p):
        return C2POArithmeticSubtract(p.lineno, p[0], p[2])

    @_("expr ARITH_MUL expr")
    def expr(self, p):
        return C2POArithmeticMultiply(p.lineno, p[0], p[2])

    @_("expr ARITH_DIV expr")
    def expr(self, p):
        return C2POArithmeticMultiply(p.lineno, p[0], p[2])

    @_("expr ARITH_MOD expr")
    def expr(self, p):
        return C2POArithmeticModulo(p.lineno, p[0], p[2])

    # Unary temporal expressions
    @_("TL_GLOBAL interval expr")
    def expr(self, p):
        return C2POGlobal(p.lineno, p[2], p[1].lb, p[1].ub)

    @_("TL_FUTURE interval expr")
    def expr(self, p):
        return C2POFuture(p.lineno, p[2], p[1].lb, p[1].ub)

    @_("TL_HIST interval expr")
    def expr(self, p):
        return C2POHistorical(p.lineno, p[2], p[1].lb, p[1].ub)

    @_("TL_ONCE interval expr")
    def expr(self, p):
        return C2POOnce(p.lineno, p[2], p[1].lb, p[1].ub)

    # Binary temporal expressions
    @_("expr TL_UNTIL interval expr")
    def expr(self, p):
        return C2POUntil(p.lineno, p[0], p[3], p[2].lb, p[2].ub)

    @_("expr TL_RELEASE interval expr")
    def expr(self, p):
        return C2PORelease(p.lineno, p[0], p[3], p[2].lb, p[2].ub)

    @_("expr TL_SINCE interval expr")
    def expr(self, p):
        return C2POSince(p.lineno, p[0], p[3], p[2].lb, p[2].ub)

    # Parentheses
    @_("LPAREN expr RPAREN")
    def expr(self, p):
        return p[1]

    # Symbol
    @_("TL_TRUE")
    def expr(self, p):
        return C2POBool(p.lineno, True)

    # Symbol
    @_("TL_FALSE")
    def expr(self, p):
        return C2POBool(p.lineno, False)

    # Symbol
    @_("SYMBOL")
    def expr(self, p):
        if p[0] in self.literals:
            if self.literals[p[0]] is C2POSignal:
                return C2POSignal(p.lineno, p[0], C2PONoType())
            elif self.literals[p[0]] is C2POAtomicChecker:
                return C2POAtomicChecker(p.lineno, p[0])
        return C2POVariable(p.lineno, p[0])

    # Integer
    @_("NUMERAL")
    def expr(self, p):
        return C2POInteger(p.lineno, int(p[0]))

    # Float
    @_("DECIMAL")
    def expr(self, p):
        return C2POFloat(p.lineno, float(p[0]))
        
    # Shorthand interval
    @_("LBRACK bound RBRACK")
    def interval(self, p):
        return Interval(0, p[1])

    # Standard interval
    @_("LBRACK bound COMMA bound RBRACK")
    def interval(self, p):
        return Interval(p[1], p[3])

    @_("NUMERAL")
    def bound(self, p):
        return int(p[0])

    @_("TL_MISSION_TIME")
    def bound(self, p):
        if self.mission_time < 0:
            logger.error(f"{p.lineno}: Mission time used but not set. Set using the '--mission-time' option.")
            self.status = False
        return self.mission_time


def parse_c2po(input_path: Path, mission_time: int) -> Optional[C2POProgram]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    with open(input_path, "r") as f:
        contents = f.read()

    lexer: C2POLexer = C2POLexer()
    parser: C2POParser = C2POParser(mission_time)
    sections: List[C2POSection] = parser.parse(lexer.tokenize(contents))

    if not parser.status:
        return None

    return C2POProgram(0, sections)


class MLTLLexer(Lexer):

    tokens = { TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE, TL_UNTIL, TL_RELEASE, TL_SINCE, 
               TL_MISSION_TIME, TL_TRUE, TL_FALSE, TL_ATOMIC,
               LOG_NEG, LOG_AND, LOG_OR, LOG_IMPL, LOG_IFF, 
               NEWLINE, NUMERAL, COMMA, LBRACK, RBRACK, LPAREN, RPAREN }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r"\#.*\n"

    # Propositional logic ops/literals
    LOG_NEG  = r"!"
    LOG_AND  = r"&"
    LOG_OR   = r"\|"
    LOG_IMPL = r"->"
    LOG_IFF  = r"<->"

    # Others
    NEWLINE = r"\n"
    NUMERAL = r"[1-9][0-9]*|0"
    COMMA   = r","
    LBRACK  = r"\["
    RBRACK  = r"\]"
    LPAREN  = r"\("
    RPAREN  = r"\)"

    # Keywords
    TL_MISSION_TIME = r"M"
    TL_GLOBAL  = r"G"
    TL_FUTURE  = r"F"
    TL_HIST    = r"H"
    TL_ONCE    = r"O"
    TL_UNTIL   = r"U"
    TL_RELEASE = r"R"
    TL_SINCE   = r"S"
    TL_TRUE    = r"true"
    TL_FALSE   = r"false"
    TL_ATOMIC  = r"a([1-9][0-9]*|0)"

    # Extra action for newlines
    def NEWLINE(self, t):
        self.lineno += t.value.count("\n")
        return t

    def error(self, t):
        logger.error(f"{self.lineno}: Illegal character '%s' {t.value[0]}")
        self.index += 1


class MLTLParser(Parser):
    tokens = MLTLLexer.tokens

    # Using C operator precedence as a guide
    precedence = (
        ("left", LOG_IMPL, LOG_IFF),
        ("left", LOG_OR),
        ("left", LOG_AND),
        ("left", TL_UNTIL, TL_RELEASE, TL_SINCE),
        ("right", LOG_NEG, TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE),
        ("right", LPAREN)
    )

    def __init__(self, mt: int) :
        super().__init__()
        self.mission_time = mt
        self.spec_num: int = 0
        self.atomics = set()
        self.is_ft = False
        self.is_pt = False
        self.status = True

    def error(self, token):
        self.status = False
        lineno = getattr(token, "lineno", 0)
        if token:
            logger.error(f"{lineno}: Syntax error, token='{token.value}'")
        else:
            logger.error(f"{lineno}: Syntax error, token is 'None'")

    @_("spec_list")
    def program(self, p):
        declaration = [C2POVariableDeclaration(0, list(self.atomics), C2POBoolType(False))]
        input_section = C2POInputSection(0, declaration)

        if self.is_pt:
            spec_section = C2POPastTimeSpecSection(0, p[0])
        else:
            spec_section = C2POFutureTimeSpecSection(0, p[0])

        # "a0" -> 0
        # "a1" -> 1
        # ...
        signal_mapping = { a:int(a[1:]) for a in self.atomics }

        return ([input_section, spec_section], signal_mapping)

    @_("spec_list spec")
    def spec_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def spec_list(self, p):
        return []

    @_("expr NEWLINE")
    def spec(self, p):
        self.spec_num += 1
        return C2POSpecification(p.lineno, "", self.spec_num-1, p[0])

    # Unary expressions
    @_("LOG_NEG expr")
    def expr(self, p):
        return C2POLogicalNegate(p.lineno, p[1])

    # Binary expressions
    @_("expr LOG_IMPL expr")
    def expr(self, p):
        return C2POLogicalImplies(p.lineno, p[0], p[2])

    @_("expr LOG_IFF expr")
    def expr(self, p):
        return C2POLogicalIff(p.lineno, p[0], p[2])

    @_("expr LOG_OR expr")
    def expr(self, p):
        return C2POLogicalOr(p.lineno, [p[0], p[2]])

    @_("expr LOG_AND expr")
    def expr(self, p):
        return C2POLogicalAnd(p.lineno, [p[0], p[2]])

    # Unary temporal expressions
    @_("TL_GLOBAL interval expr")
    def expr(self, p):
        self.is_ft = True
        if self.is_pt:
            logger.error(f"{p.lineno}: Mixing past and future time formula not allowed.")
            self.status = False

        return C2POGlobal(p.lineno, p[2], p[1].lb, p[1].ub)

    @_("TL_FUTURE interval expr")
    def expr(self, p):
        self.is_ft = True
        if self.is_pt:
            logger.error(f"{p.lineno}: Mixing past and future time formula not allowed.")
            self.status = False

        return C2POFuture(p.lineno, p[2], p[1].lb, p[1].ub)

    @_("TL_HIST interval expr")
    def expr(self, p):
        self.is_pt = True
        if self.is_ft:
            logger.error(f"{p.lineno}: Mixing past and future time formula not allowed.")
            self.status = False

        return C2POHistorical(p.lineno, p[2], p[1].lb, p[1].ub)

    @_("TL_ONCE interval expr")
    def expr(self, p):
        self.is_pt = True
        if self.is_ft:
            logger.error(f"{p.lineno}: Mixing past and future time formula not allowed.")
            self.status = False

        return C2POOnce(p.lineno, p[2], p[1].lb, p[1].ub)

    # Binary temporal expressions
    @_("expr TL_UNTIL interval expr")
    def expr(self, p):
        self.is_ft = True
        if self.is_pt:
            logger.error(f"{p.lineno}: Mixing past and future time formula not allowed.")
            self.status = False

        return C2POUntil(p.lineno, p[0], p[3], p[2].lb, p[2].ub)

    @_("expr TL_RELEASE interval expr")
    def expr(self, p):
        self.is_ft = True
        if self.is_pt:
            logger.error(f"{p.lineno}: Mixing past and future time formula not allowed.")
            self.status = False

        return C2PORelease(p.lineno, p[0], p[3], p[2].lb, p[2].ub)

    @_("expr TL_SINCE interval expr")
    def expr(self, p):
        self.is_pt = True
        if self.is_ft:
            logger.error(f"{p.lineno}: Mixing past and future time formula not allowed.")
            self.status = False

        return C2POSince(p.lineno, p[0], p[3], p[2].lb, p[2].ub)

    # Parentheses
    @_("LPAREN expr RPAREN")
    def expr(self, p):
        return p[1]

    @_("TL_TRUE")
    def expr(self, p):
        return C2POBool(p.lineno, True)

    @_("TL_FALSE")
    def expr(self, p):
        return C2POBool(p.lineno, False)

    @_("TL_ATOMIC")
    def expr(self, p):
        self.atomics.add(p[0])
        return C2POSignal(p.lineno, p[0], C2PONoType())

    # Shorthand interval
    @_("LBRACK bound RBRACK")
    def interval(self, p):
        return Interval(0, p[1])

    # Standard interval
    @_("LBRACK bound COMMA bound RBRACK")
    def interval(self, p):
        return Interval(p[1], p[3])

    @_("NUMERAL")
    def bound(self, p):
        return int(p[0])

    @_("TL_MISSION_TIME")
    def bound(self, p):
        if self.mission_time < 0:
            logger.error(f"{p.lineno}: Mission time used but not set. Set using the '--mission-time' option.")
            self.status = False
        return self.mission_time


def parse_mltl(input_path: Path, mission_time: int) -> Optional[Tuple[C2POProgram, Dict[str, int]]]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    with open(input_path, "r") as f:
        contents = f.read()

    lexer: MLTLLexer = MLTLLexer()
    parser: MLTLParser = MLTLParser(mission_time)
    output: Tuple[List[C2POSection], Dict[str, int]] = parser.parse(lexer.tokenize(contents))

    if output:
        sections, signal_mapping = output

    if not parser.status:
        return None

    return (C2POProgram(0, sections), signal_mapping)