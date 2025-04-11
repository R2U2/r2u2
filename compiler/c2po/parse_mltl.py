#type: ignore
from __future__ import annotations
from typing import Optional
from pathlib import Path

from c2po import sly, types, cpt, log

MODULE_CODE = "PRSM"

class MLTLLexer(sly.Lexer):

    tokens = { TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE, TL_UNTIL, TL_RELEASE, TL_SINCE, TL_TRIGGER,
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
    TL_TRIGGER = r"T"
    TL_TRUE    = r"true"
    TL_FALSE   = r"false"
    TL_ATOMIC  = r"a([1-9][0-9]*|0)"

    # Extra action for newlines
    def NEWLINE(self, t):
        self.lineno += t.value.count("\n")
        return t

    def __init__(self, filename: str):
        super().__init__()
        self.filename = filename

    def error(self, t):
        log.error(MODULE_CODE, f"Illegal character '%s' {t.value[0]}", log.FileLocation(self.filename, t.lineno))
        self.index += 1


class MLTLParser(sly.Parser):
    tokens = MLTLLexer.tokens

    # Using C operator precedence as a guide
    precedence = (
        ("left", LOG_IMPL, LOG_IFF),
        ("left", LOG_OR),
        ("left", LOG_AND),
        ("left", TL_UNTIL, TL_RELEASE, TL_SINCE, TL_TRIGGER),
        ("right", LOG_NEG, TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE),
        ("right", LPAREN)
    )

    def __init__(self, filename: str, mission_time: int) :
        super().__init__()
        self.filename = filename
        self.mission_time = mission_time
        self.spec_num: int = 0
        self.atomics = set()
        self.is_ft = False
        self.is_pt = False
        self.status = True

    def error(self, token):
        self.status = False
        lineno = getattr(token, "lineno", 0)
        if token:
            log.error(MODULE_CODE, f"Syntax error, unexpected token='{token.value}'", 
                      log.FileLocation(self.filename, lineno)
            )
        else:
            log.error(MODULE_CODE, f"Syntax error, token is 'None'"
                      f"\n\tDid you forget to end the last formula with a newline?", 
                      log.FileLocation(self.filename, lineno)
            )

    def fresh_label(self) -> str:
        return f"__f{self.spec_num}__"

    @_("spec_list")
    def program(self, p):
        declaration = [cpt.VariableDeclaration(0, list(self.atomics), types.BoolType())]
        input_section = cpt.InputSection(0, declaration)

        if self.is_pt:
            spec_section = cpt.PastTimeSpecSection(0, p[0])
        else:
            spec_section = cpt.FutureTimeSpecSection(0, p[0])

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
        self.is_ft = True
        if self.is_pt:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Global(log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2])

    @_("TL_FUTURE interval expr")
    def expr(self, p):
        self.is_ft = True
        if self.is_pt:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Future(log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2])

    @_("TL_HIST interval expr")
    def expr(self, p):
        self.is_pt = True
        if self.is_ft:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Historical(log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2])

    @_("TL_ONCE interval expr")
    def expr(self, p):
        self.is_pt = True
        if self.is_ft:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Once(log.FileLocation(self.filename, p.lineno), p[1].lb, p[1].ub, p[2])

    # Binary temporal expressions
    @_("expr TL_UNTIL interval expr")
    def expr(self, p):
        self.is_ft = True
        if self.is_pt:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Until(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])

    @_("expr TL_RELEASE interval expr")
    def expr(self, p):
        self.is_ft = True
        if self.is_pt:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Release(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])

    @_("expr TL_SINCE interval expr")
    def expr(self, p):
        self.is_pt = True
        if self.is_ft:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Since(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])
    
    @_("expr TL_TRIGGER interval expr")
    def expr(self, p):
        self.is_pt = True
        if self.is_ft:
            log.error(MODULE_CODE, f"Mixing past and future time formula not allowed.", log.FileLocation(self.filename, p.lineno))
            self.status = False

        return cpt.TemporalOperator.Trigger(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[0], p[3])

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
        return int(p[0])

    @_("TL_MISSION_TIME")
    def bound(self, p):
        if self.mission_time < 0:
            log.error(MODULE_CODE, f"Mission time used but not set. Set using the '--mission-time' option.", log.FileLocation(self.filename, p.lineno))
            self.status = False
        return self.mission_time


def parse_mltl(input_path: Path, mission_time: int) -> Optional[tuple[cpt.Program, dict[str, int]]]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    log.debug(MODULE_CODE, 1, f"Parsing {input_path}")
    
    with open(input_path, "r") as f:
        contents = f.read()

    lexer: MLTLLexer = MLTLLexer(str(input_path))
    parser: MLTLParser = MLTLParser(str(input_path), mission_time)
    output: tuple[list[cpt.C2POSection], dict[str, int]] = parser.parse(lexer.tokenize(contents))

    if output:
        sections, signal_mapping = output

    if not parser.status:
        return None

    sections, signal_mapping = output

    return (cpt.Program(0, sections), signal_mapping)