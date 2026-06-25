#type: ignore
from __future__ import annotations
from typing import Optional, Any

from c2po import sly
from c2po import types, cpt, log, type_check

class EgglogOutputLexer(sly.Lexer):
    tokens = { 
        # Operators
        OP_IMPLIES, OP_NOT, OP_AND, OP_OR, OP_EQUIV,
        # Temporal operators (only future-time operators from MLTL datatype)
        OP_FUTURE, OP_GLOBAL, OP_UNTIL, OP_RELEASE,
        # Keywords
        KW_VAR, KW_INTERVAL, KW_BOOL,
        # Literals
        STRING, NUMERAL, BOOL_TRUE, BOOL_FALSE,
        # Punctuation
        LPAREN, RPAREN
    }

    # String containing ignored characters between tokens
    ignore = " \t\n"

    # Operators
    OP_IMPLIES = r"Implies"
    OP_NOT = r"Not"
    OP_EQUIV = r"Equiv"
    OP_AND = r"And\d+"
    OP_OR = r"Or\d+"
    
    # Temporal operators (only future-time from MLTL datatype)
    OP_FUTURE = r"Future"
    OP_GLOBAL = r"Global"
    OP_UNTIL = r"Until"
    OP_RELEASE = r"Release"
    
    # Keywords
    KW_VAR = r"Var"
    KW_INTERVAL = r"Interval"
    KW_BOOL = r"Bool"
    
    # Literals
    STRING = r'"[^"]*"'
    NUMERAL = r"[0-9]+"
    BOOL_TRUE = r"true"
    BOOL_FALSE = r"false"
    
    # Punctuation
    LPAREN = r"\("
    RPAREN = r"\)"

    def __init__(self, filename: str):
        super().__init__()
        self.filename = filename

    def error(self, t):
        log.error(f"illegal character '{t.value[0]}'", log.FileLocation(self.filename, t.lineno))
        self.index += 1


class EgglogOutputParser(sly.Parser):
    tokens = EgglogOutputLexer.tokens

    def __init__(self, filename: str):
        super().__init__()
        self.filename = filename
        self.status = True
        self.atomics = set()

    def error(self, token):
        self.status = False
        lineno = getattr(token, "lineno", 0)
        if token:
            log.error(f"syntax error, unexpected token='{token.value}'", 
                      log.FileLocation(self.filename, lineno)
            )
        else:
            log.error(f"syntax error, token is 'None' (EOF)"
                      "\n\tDid you forget to end the expression?", 
                      log.FileLocation(self.filename, lineno)
            )

    @_("expr")
    def program(self, p):
        return p[0]

    # Logical operators - S-expression format: (Operator args...)
    @_("LPAREN OP_IMPLIES expr expr RPAREN")
    def expr(self, p):
        return cpt.Operator.LogicalImplies(log.FileLocation(self.filename, p.lineno), p[2], p[3])

    @_("LPAREN OP_EQUIV expr expr RPAREN")
    def expr(self, p):
        return cpt.Operator.LogicalIff(log.FileLocation(self.filename, p.lineno), p[2], p[3])

    @_("LPAREN OP_NOT expr RPAREN")
    def expr(self, p):
        return cpt.Operator.LogicalNegate(log.FileLocation(self.filename, p.lineno), p[2])

    @_("LPAREN OP_AND expr_list RPAREN")
    def expr(self, p):
        return cpt.Operator.LogicalAnd(log.FileLocation(self.filename, p.lineno), p[2])

    @_("LPAREN OP_OR expr_list RPAREN")
    def expr(self, p):
        return cpt.Operator.LogicalOr(log.FileLocation(self.filename, p.lineno), p[2])

    # Temporal operators (unary) - S-expression format: (Operator interval expr)
    @_("LPAREN OP_FUTURE interval expr RPAREN")
    def expr(self, p):
        return cpt.TemporalOperator.Future(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[3])

    @_("LPAREN OP_GLOBAL interval expr RPAREN")
    def expr(self, p):
        return cpt.TemporalOperator.Global(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[3])

    # Temporal operators (binary) - S-expression format: (Operator interval expr expr)
    @_("LPAREN OP_UNTIL interval expr expr RPAREN")
    def expr(self, p):
        return cpt.TemporalOperator.Until(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[3], p[4])

    @_("LPAREN OP_RELEASE interval expr expr RPAREN")
    def expr(self, p):
        return cpt.TemporalOperator.Release(log.FileLocation(self.filename, p.lineno), p[2].lb, p[2].ub, p[3], p[4])

    # Boolean constants - S-expression format: (Bool true) or (Bool false)
    @_("LPAREN KW_BOOL BOOL_TRUE RPAREN")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), True)

    @_("LPAREN KW_BOOL BOOL_FALSE RPAREN")
    def expr(self, p):
        return cpt.Constant(log.FileLocation(self.filename, p.lineno), False)

    # Variable - in S-expression format: (Var "name")
    @_("LPAREN KW_VAR STRING RPAREN")
    def expr(self, p):
        # Remove quotes from string
        var_name = p[2][1:-1]
        self.atomics.add(var_name)
        return cpt.Signal(log.FileLocation(self.filename, p.lineno), var_name, types.NoType())

    # Interval - in S-expression format: (Interval lb ub)
    @_("LPAREN KW_INTERVAL NUMERAL NUMERAL RPAREN")
    def interval(self, p):
        lb = int(p[2])
        ub = int(p[3])
        return cpt.ConcreteInterval(lb, ub)

    # Expression list (space-separated)
    @_("expr_list expr")
    def expr_list(self, p):
        return p[0] + [p[1]]

    @_("expr")
    def expr_list(self, p):
        return [p[0]]


def parse(egglog_output: str, context: cpt.Context, options: dict[str, Any]) -> Optional[cpt.Expression]:
    """Parse egglog output string and returns corresponding expression on success, else returns None.
    
    `options` is a dictionary of options that must contain the following key (same as those needed for type checking):
    - `spec_filename`: The path to the specification file
    """
    log.debug(1, "parsing egglog output")
    
    contents = egglog_output.strip()

    lexer: EgglogOutputLexer = EgglogOutputLexer("")
    parser: EgglogOutputParser = EgglogOutputParser("")
    output: cpt.Expression = parser.parse(lexer.tokenize(contents))

    if not parser.status:
        return None

    exprs_in_use: set[cpt.Expression] = set()
    for expr in cpt.postorder(output, context):
        exprs_in_use.add(expr)

    # Replace atomics with their corresponding expressions
    for expr in cpt.postorder(output, context):
        if not isinstance(expr, cpt.Signal):
            continue

        aid = int(str(expr)[1:]) # atomics are of the form 'a<id>'
        new_expr = context.atomic_expr_map[aid]
        expr.replace(new_expr)

        # Clear unused parents of atomic expression from the original expression
        to_remove = set()
        for parent in new_expr.parents:
            if parent not in exprs_in_use:
                to_remove.add(parent)
        for parent in to_remove:
            new_expr.parents.remove(parent)

    # Compute types for the new expression
    if not type_check.type_check_expr(output, context, options):
        log.error("failed to type check egglog output")
        return None

    return output

