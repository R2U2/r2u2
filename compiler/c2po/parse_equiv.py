#type: ignore
from __future__ import annotations
from typing import Optional, Any
from c2po import sly
from c2po import types, cpt, log, command, util

class MLTLEquivLexer(sly.Lexer):

    tokens = { TL_GLOBAL, TL_FUTURE, TL_UNTIL, TL_RELEASE, 
               # TL_HIST, TL_ONCE, TL_SINCE, TL_TRIGGER,
               TL_MISSION_TIME, TL_TRUE, TL_FALSE, TL_ATOMIC, TL_BOUND,
               LOG_NEG, LOG_AND, LOG_OR, LOG_IMPL, LOG_IFF, 
               REL_EQ, REL_NEQ, REL_GTE, REL_LTE, REL_GT, REL_LT,
               ARITH_ADD, ARITH_SUB, ARITH_MUL, ARITH_DIV, MIN, MAX,
               NEWLINE, NUMERAL, COMMA, LBRACK, RBRACK, LPAREN, RPAREN, CONSTRAINT_LABEL }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r"\#.*\n"

    CONSTRAINT_LABEL = r"c:"

    REL_NEQ = r"!=" # longer tokens must come first
    NUMERAL = r"[1-9][0-9]*|0"

    # Propositional logic ops/literals
    LOG_NEG  = r"!"
    LOG_AND  = r"&"
    LOG_OR   = r"\|"
    LOG_IMPL = r"->"
    LOG_IFF  = r"<->"

    # Relational ops
    REL_EQ  = r"="
    REL_GTE = r">="
    REL_LTE = r"<=" 
    REL_GT  = r">"
    REL_LT  = r"<"

    # Arithmetic ops
    ARITH_ADD   = r"\+"
    ARITH_SUB   = r"-"
    ARITH_MUL   = r"\*"
    ARITH_DIV   = r"/"

    # Arithmetic ops
    MIN   = r"min"
    MAX   = r"max"

    # Others
    NEWLINE = r"\n"
    COMMA   = r","
    LBRACK  = r"\["
    RBRACK  = r"\]"
    LPAREN  = r"\("
    RPAREN  = r"\)"

    # Keywords
    TL_MISSION_TIME = r"M"
    TL_GLOBAL  = r"G"
    TL_FUTURE  = r"F"
    TL_UNTIL   = r"U"
    TL_RELEASE = r"R"
    # TL_HIST    = r"H"
    # TL_ONCE    = r"O"
    # TL_SINCE   = r"S"
    # TL_TRIGGER = r"T"
    TL_TRUE    = r"true"
    TL_FALSE   = r"false"
    TL_ATOMIC  = r"a([1-9][0-9]*|0)"
    TL_BOUND  = r"b([1-9][0-9]*|0)"

    # Extra action for newlines
    def NEWLINE(self, t):
        self.lineno += t.value.count("\n")
        return t

    def __init__(self, filename: str):
        super().__init__()
        self.filename = filename

    def error(self, t):
        log.error(f"illegal character '{t.value[0]}'", log.FileLocation(self.filename, t.lineno))
        self.index += 1


class MLTLEquivParser(sly.Parser):
    tokens = MLTLEquivLexer.tokens

    # Using C operator precedence as a guide
    precedence = (
        ("left", LOG_IMPL, LOG_IFF),
        ("left", LOG_OR),
        ("left", LOG_AND),
        ("left", TL_UNTIL, TL_RELEASE),
        ("left", REL_EQ, REL_NEQ),
        ("left", REL_GT, REL_LT, REL_GTE, REL_LTE),
        ("left", ARITH_ADD, ARITH_SUB, ARITH_MUL, ARITH_DIV),
        ("right", LOG_NEG, TL_GLOBAL, TL_FUTURE),
        ("right", LPAREN, MIN, MAX)
    )

    def __init__(self, filename: str) :
        super().__init__()
        self.filename = filename
        self.spec_num: int = 0
        self.atomics = set()
        self.bounds = []
        self.constraints = []
        self.is_ft = False
        self.is_pt = False
        self.status = True

    def error(self, token):
        self.status = False
        lineno = getattr(token, "lineno", 0)
        if token:
            log.error(f"syntax error, unexpected token='{token.value}'", 
                      log.FileLocation(self.filename, lineno)
            )
        else:
            log.error(f"syntax error, token is 'None' (EOF)"
                      f"\n\tDid you forget to end the last formula with a newline?", 
                      log.FileLocation(self.filename, lineno)
            )

    def fresh_label(self) -> str:
        return f"__f{self.spec_num}__"

    @_("constraint_list spec_list")
    def program(self, p):
        self.constraints = p[0]
        declaration = [cpt.VariableDeclaration(0, list(self.atomics), types.BoolType())]
        input_section = cpt.InputSection(0, declaration)
        spec_section = cpt.FutureTimeSpecSection(0, p[1])

        # "a0" -> 0
        # "a1" -> 1
        # ...
        signal_mapping = { a:int(a[1:]) for a in self.atomics }

        return cpt.Program(log.FileLocation(self.filename, 0), [input_section, spec_section]), signal_mapping

    @_("constraint_list constraint")
    def constraint_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def constraint_list(self, p):
        return []

    @_("CONSTRAINT_LABEL constraint_expr NEWLINE")
    def constraint(self, p):
        return p[1]

    @_("constraint_expr REL_EQ constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.Equal(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("constraint_expr REL_NEQ constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.NotEqual(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("constraint_expr REL_GTE constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.GreaterThanOrEqual(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("constraint_expr REL_LTE constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.LessThanOrEqual(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("constraint_expr REL_GT constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.GreaterThan(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("constraint_expr REL_LT constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.LessThan(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("constraint_expr ARITH_ADD constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.ArithmeticAdd(log.FileLocation(self.filename, p.lineno), [p[0], p[2]])

    @_("constraint_expr ARITH_SUB constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.ArithmeticSubtract(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("constraint_expr ARITH_MUL constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.ArithmeticMultiply(log.FileLocation(self.filename, p.lineno), [p[0], p[2]])

    @_("constraint_expr ARITH_DIV constraint_expr")
    def constraint_expr(self, p):
        return cpt.Operator.ArithmeticDivide(log.FileLocation(self.filename, p.lineno), p[0], p[2])

    @_("MIN LPAREN constraint_expr COMMA constraint_expr RPAREN")
    def constraint_expr(self, p):
        return cpt.Operator.Min(log.FileLocation(self.filename, p.lineno), [p[2], p[4]])
    
    @_("MAX LPAREN constraint_expr COMMA constraint_expr RPAREN")
    def constraint_expr(self, p):
        return cpt.Operator.Max(log.FileLocation(self.filename, p.lineno), [p[2], p[4]])

    @_("LPAREN constraint_expr RPAREN")
    def constraint_expr(self, p):
        return p[1]

    @_("TL_BOUND")
    def constraint_expr(self, p):
        bound = cpt.SymbolicIntervalVariable(log.FileLocation(self.filename, p.lineno), p[0])
        if bound not in self.bounds:
            self.bounds.append(bound)
        return bound

    @_("NUMERAL")
    def constraint_expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), int(p[0]))

    @_("TL_MISSION_TIME")
    def constraint_expr(self, p):
        return cpt.MissionTime(log.FileLocation(self.filename, p.lineno))

    @_("spec_list spec")
    def spec_list(self, p):
        return p[0] + [p[1]]

    @_("")
    def spec_list(self, p):
        return []

    @_("expr NEWLINE")
    def spec(self, p):
        self.spec_num += 1
        return cpt.Formula(log.FileLocation(self.filename, p.lineno), self.fresh_label(), self.spec_num-1, p[0])

    # Unary expressions
    @_("LOG_NEG expr")
    def expr(self, p):
        return cpt.Operator.LogicalNegate(log.FileLocation(self.filename, p.lineno), p[1])

    # Binary expressions
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

    # Unary temporal expressions
    @_("TL_GLOBAL interval expr")
    def expr(self, p):
        return cpt.SymbolicTemporalOperator.Global(
            log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2]
        )

    @_("TL_FUTURE interval expr")
    def expr(self, p):
        return cpt.SymbolicTemporalOperator.Future(
            log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2]
        )

    # Binary temporal expressions
    @_("expr TL_UNTIL interval expr")
    def expr(self, p):
        return cpt.SymbolicTemporalOperator.Until(
            log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3]
        )

    @_("expr TL_RELEASE interval expr")
    def expr(self, p):
        return cpt.SymbolicTemporalOperator.Release(
            log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3]
        )

    # Parentheses
    @_("LPAREN expr RPAREN")
    def expr(self, p):
        return p[1]

    @_("TL_TRUE")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), True)

    @_("TL_FALSE")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), False)

    @_("TL_ATOMIC")
    def expr(self, p):
        self.atomics.add(p[0])
        return cpt.Signal(log.FileLocation(self.filename, p.lineno), p[0], types.NoType())

    # Standard interval
    @_("LBRACK constraint_expr COMMA constraint_expr RBRACK")
    def interval(self, p):
        return cpt.SymbolicInterval(p[1], p[3])


def parse_equiv(context: cpt.Context, options: dict[str, Any]) -> Optional[cpt.Program]:
    """Parse contents of equivalence specification and returns corresponding program on success, else returns None."""
    contents = util.read_file(options["filename"])
    if contents is None:
        return None
        
    context.set_spec_filename(options["filename"])

    lexer: MLTLEquivLexer = MLTLEquivLexer(options["filename"])
    parser: MLTLEquivParser = MLTLEquivParser(options["filename"])
    output: tuple[cpt.Program, types.SignalMapping] = parser.parse(lexer.tokenize(contents))

    if not parser.status:
        return None

    program, signal_mapping = output
    context.bounds = parser.bounds
    context.constraints = parser.constraints
    context.signal_mapping = signal_mapping

    log.debug(1, f"constraints: {context.constraints}")
    log.debug(1, f"bounds: {context.bounds}")

    return program

parse_equiv_command = command.Command(
    name="parse_equiv",
    description="Parse a MLTL equivalence specification and return a program",
    options=[
        {
            "name": "filename",
            "description": "The path to the MLTL equivalence specification file",
            "required": True,
            "type": str,
            "default": None,
            "choices": None,
        }
    ],
    func=lambda program, context, options: parse_equiv(context, options),
    guards=[],
)
command.CommandRegistry.register(parse_equiv_command)
