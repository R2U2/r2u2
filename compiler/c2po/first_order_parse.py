#type: ignore
from __future__ import annotations
import pathlib
from typing import Optional
import re

from c2po import sly, types, cpt, log

MODULE_CODE = "FOPS"


def parse_bounds_file(bounds_path: pathlib.Path) -> Optional[dict[str,int]]:
    """Return the bounds mapping from `bounds_path`."""
    with open(bounds_path, "r") as f:
        content: str = f.read()

    bounds: dict[str,int] = {}

    lines = content.splitlines()
    for line in lines:
        if re.match(r"[a-zA-Z_][a-zA-Z0-9_\[\]]*=\d+", line):
            strs = line.split("=")
            id = strs[0]
            bnd = int(strs[1])

            if id in bounds:
                log.warning(
                    MODULE_CODE,
                    f"Bounded guard '{id}' found multiple times in bounds file, using latest value",
                    log.FileLocation(bounds_path.name, lines.index(line) + 1),
                )

            if bnd < 1:
                log.error(
                    MODULE_CODE,
                    f"Invalid bound value for guard '{id}' (found {bnd}, must be greater than 0)",
                    log.FileLocation(bounds_path.name, lines.index(line) + 1),
                )
                return None

            bounds[id] = bnd
        else:
            log.error(
                MODULE_CODE,
                f"Invalid format for bounds line (found {line})"
                "\n\t Should be of the form SYMBOL '=' NUMERAL",
                log.FileLocation(bounds_path.name, lines.index(line)),
            )
            return None

    return bounds


class FormulaLexer(sly.Lexer):

    tokens = { TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE, TL_UNTIL, TL_RELEASE, TL_SINCE, 
               TL_MISSION_TIME, TL_TRUE, TL_FALSE, SYMBOL, 
               TL_EXISTS, TL_FORALL,
               REL_EQ, REL_NEQ, REL_GTE, REL_LTE, REL_GT, REL_LT,
               ARITH_ADD, ARITH_SUB, ARITH_MUL, ARITH_DIV, ARITH_MOD,
               LOG_NEG, LOG_AND, LOG_OR, LOG_IMPL, LOG_IFF, 
               NUMERAL, COMMA, LBRACK, RBRACK, LPAREN, RPAREN, COLON }

    # String containing ignored characters between tokens
    ignore = " \t\n"
    ignore_comment = r"//.*\n"

    # Relational ops
    REL_EQ  = r"=="
    REL_NEQ = r"!="
    REL_GTE = r">=|≥"
    REL_LTE = r"<=|≤" 
    REL_GT  = r">"
    REL_LT  = r"<"

    # Propositional logic ops/literals
    LOG_NEG  = r"!"
    LOG_AND  = r"&"
    LOG_OR   = r"\|"
    LOG_IMPL = r"->"
    LOG_IFF  = r"<->"

    # Arithmetic ops
    ARITH_ADD   = r"\+"
    ARITH_SUB   = r"-"
    ARITH_MUL   = r"\*|•|⋅"
    ARITH_DIV   = r"/|÷"
    ARITH_MOD   = r"%"

    # Others
    NEWLINE = r"\n"
    NUMERAL = r"[1-9][0-9]*|0"
    COLON   = r":"
    COMMA   = r","
    LBRACK  = r"\["
    RBRACK  = r"\]"
    LPAREN  = r"\("
    RPAREN  = r"\)"

    SYMBOL  = r"[a-zA-Z_][a-zA-Z0-9_]*"

    SYMBOL['forall'] = TL_FORALL
    SYMBOL['exists'] = TL_EXISTS
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
    def NEWLINE(self, t):
        self.lineno += t.value.count("\n")
        return t

    def __init__(self, filename: str):
        super().__init__()
        self.filename = filename

    def error(self, t):
        log.error(MODULE_CODE, f"Illegal character '%s' {t.value[0]}", log.FileLocation(self.filename, t.lineno))
        self.index += 1


class FormulaParser(sly.Parser):
    tokens = FormulaLexer.tokens

    # Using C operator precedence as a guide
    precedence = (
        ("left", LOG_IMPL, LOG_IFF),
        ("left", LOG_OR),
        ("left", LOG_AND),
        ("left", TL_UNTIL, TL_RELEASE, TL_SINCE),
        ("left", REL_EQ, REL_NEQ),
        ("left", REL_GT, REL_LT, REL_GTE, REL_LTE),
        ("left", ARITH_ADD, ARITH_SUB),
        ("left", ARITH_MUL, ARITH_DIV, ARITH_MOD),
        ("right", LOG_NEG, UNARY_ARITH_SUB, TL_GLOBAL, TL_FUTURE, TL_HIST, TL_ONCE),
        ("right", LPAREN, LBRACK)
    )

    def __init__(self, filename: str, bounds: dict[str,int], mission_time: int) :
        super().__init__()
        self.filename = filename
        self.bounds = bounds
        self.mission_time = mission_time
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

    @_("expr")
    def formula(self, p):
        return cpt.Formula(log.FileLocation(self.filename, p.lineno), "", 0, p[0])

    # Quantifiers
    @_("TL_FORALL LPAREN SYMBOL COLON SYMBOL RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        if p[4] not in self.bounds:
            log.error(
                MODULE_CODE, 
                f"Predicate '{p[4]}' not found in bounds file", 
                log.FileLocation(self.filename, p.lineno)
            )
            self.status = False
        boundvar = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[2])
        return cpt.Quantifier.ForAll(log.FileLocation(self.filename, p.lineno), boundvar, p[4], p[7])
    
    @_("TL_EXISTS LPAREN SYMBOL COLON SYMBOL RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        if p[4] not in self.bounds:
            log.error(
                MODULE_CODE, 
                f"Predicate '{p[4]}' not found in bounds file", 
                log.FileLocation(self.filename, p.lineno)
            )
            self.status = False
        boundvar = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[2])
        return cpt.Quantifier.Exists(log.FileLocation(self.filename, p.lineno), boundvar, p[4], p[7])
    
    @_("ARITH_SUB expr %prec UNARY_ARITH_SUB")
    def expr(self, p):
        return cpt.Operator.ArithmeticNegate(log.FileLocation(self.filename, p.lineno), p[1])
    
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

    # Unary expressions
    @_("LOG_NEG expr")
    def expr(self, p):
        return cpt.Operator.LogicalNegate(log.FileLocation(self.filename, p.lineno), p[1])
    
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
        var = cpt.Variable(log.FileLocation(self.filename, p.lineno), p[0])
        var.type = types.IntType()
        return var
    
    # Function/struct constructor expression nonempty arguments
    @_("SYMBOL LPAREN expr expr_list RPAREN")
    def expr(self, p):
        p[3].insert(0, p[2])
        return cpt.Predicate(log.FileLocation(self.filename, p.lineno), p[0], p[3])

    @_("expr_list COMMA expr")
    def expr_list(self, p):
        p[0].append(p[2])
        return p[0]

    @_("")
    def expr_list(self, p):
        return []
                
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


def parse_fo(
        formula_path: pathlib.Path, bounds_path: pathlib.Path, mission_time: int
) -> Optional[tuple[cpt.Formula, dict[str, int]]]:
    """Parse contents of input and returns corresponding first-order formula and guard bounds on success, else returns None."""
    log.debug(MODULE_CODE, 1, f"Parsing {formula_path.name} and {bounds_path.name}")
    
    with open(formula_path, "r") as f:
        contents = f.read()

    bounds: dict[str, int] = parse_bounds_file(bounds_path)
    if not bounds:
        return None

    lexer: FormulaLexer = FormulaLexer(str(formula_path))
    parser: FormulaParser = FormulaParser(str(formula_path), bounds, mission_time)
    formula: cpt.Formula = parser.parse(lexer.tokenize(contents))
    if not parser.status:
        return None

    return (formula, bounds)


