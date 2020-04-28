# ------------------------------------------------------------
# MLTLparse.py
#
# Parser for MTL formula.
# Construct observer abstract syntax tree
# Syntax : https://ti.arc.nasa.gov/m/profile/kyrozier/PANDA/PANDA.html
# Reference: https://www.dabeaz.com/ply/ply.html#ply_nn9
# ------------------------------------------------------------
import ply.yacc as yacc
from .MLTLlex import tokens
from .Observer import *
import sys

__all__ = ['status','parser']
status = 'pass'

prog = PROGRAM()

def p_program(p):
    '''
    program : program statement
            | statement
    '''
    if (len(p)==2 and p[1]):
        # p[0] = PROGRAM()
        prog.add(p[1])
        # prog = p[0]
    elif (len(p)==3):
        prog.add(p[2])

def p_statement(p):
    '''
    statement : expression SEMI
    '''
    p[0] = STATEMENT(p[1], p[2])

def p_prop_operators(p):
    '''
    expression  : expression AND expression
                | NEG expression
                | expression OR expression
                | expression EQ expression
                | expression IMPLY expression
    '''
    # Negation
    if p[1] == '!':
        p[0] = NEG(p[2])
    # elif p[1] == 'X':
    #     p[0] = GLOBAL(p[2],lb=1,ub=1)
    # Conjunction (And)
    elif len(p)>2 and p[2] == '&':
        p[0] = AND(p[1],p[3])
    # Disjunction (OR)
    elif len(p)>2 and p[2] == '|':
        # Syntactic sugar for OR, w/ just AND and NOT
         p[0] = NEG(AND(NEG(p[1]),NEG(p[3])))
        #p[0] = OR(p[1],p[3])
    # Implication
    elif p[2] == '->':
        #p[0] = IMPLY(p[1],p[3])
        # Syntactic sugar for Implies, w/ just AND and NOT
        # a0 -> a1 = !a0 | a1 = !(a0 & !a1)
        p[0] = NEG(AND(p[1],NEG(p[3])))
    # Equivalence
    elif p[2] == '<->':
        #p[0] = EQ(p[1],p[3])
        # Syntactic sugar for Equivalence, w/ just AND and NOT
        # (a0 -> a1) & (a1 -> a0) = (!a0 | a1) & (!a1 & a0) = !(a0 & !a1) & !(a1 & !a0)
        p[0] = AND(NEG(AND(p[1],NEG(p[3]))),NEG(AND(p[3],NEG(p[1]))))

def p_ftMLTL_operators(p):
    '''
    expression  : GLOBAL LBRACK NUMBER RBRACK expression
                | GLOBAL LBRACK NUMBER COMMA NUMBER RBRACK expression
                | FUTURE LBRACK NUMBER RBRACK expression
                | FUTURE LBRACK NUMBER COMMA NUMBER RBRACK expression
                | expression UNTIL LBRACK NUMBER RBRACK expression
                | expression UNTIL LBRACK NUMBER COMMA NUMBER RBRACK expression
                | expression RELEASE LBRACK NUMBER RBRACK expression
                | expression RELEASE LBRACK NUMBER COMMA NUMBER RBRACK expression
    '''
    if p[1] == 'G' and len(p) == 6:
        p[0] = GLOBAL(p[5],ub=p[3])
    elif p[1] == 'G' and len(p)==8:
        p[0] = GLOBAL(p[7],lb=p[3],ub=p[5])
    if p[1] == 'F' and len(p) == 6:
        #p[0] = FUTURE(p[5],ub=p[3])
        # Syntactic Sugar for Future just using Until
        p[0] = UNTIL(BOOL('TRUE'), p[5],ub=p[3])
    elif p[1] == 'F' and len(p)==8:
        #p[0] = FUTURE(p[7],lb=p[3],ub=p[5])
        # Syntactic Sugar for Future just using Until
        p[0] = UNTIL(BOOL('TRUE'), p[7],lb=p[3],ub=p[5])
    elif p[2] == 'U' and len(p)==7:
        p[0] = UNTIL(p[1],p[6],ub=p[4])
    elif p[2] == 'U' and len(p)==9:
        p[0] = UNTIL(p[1],p[8],lb=p[4],ub=p[6])
    elif p[2] == 'R' and len(p)==7:
        #p[0] = RELEASE(p[1],p[6],ub=p[4])
        # Syntactic Sugar for Release just using Until
        p[0] = NEG(UNTIL(NEG(p[1]),NEG(p[6]),ub=p[4]))
    elif p[2] == 'R' and len(p)==9:
        p[0] = RELEASE(p[1],p[8],lb=p[4],ub=p[6])
        # Syntactic Sugar for Release just using Until
        p[0] = NEG(UNTIL(NEG(p[1]),NEG(p[8]),lb=p[4],ub=p[6]))

def p_ptMLTL_operators(p):
    '''
    expression  : YESTERDAY expression
                | expression SINCE expression
                | expression SINCE LBRACK NUMBER COMMA NUMBER RBRACK expression
                | ONCE expression
                | ONCE LBRACK NUMBER RBRACK expression
                | ONCE LBRACK NUMBER COMMA NUMBER RBRACK expression
                | HISTORICALLY expression
                | HISTORICALLY LBRACK NUMBER RBRACK expression
                | HISTORICALLY LBRACK NUMBER COMMA NUMBER RBRACK expression
    '''
    if p[1] == 'Y':
        p[0] = YESTERDAY(p[2])
    elif p[2] == 'S':
        if len(p)==7:
            p[0] = SINCE(p[1],p[6],ub=p[4])
        elif len(p)==9:
            p[0] = SINCE(p[1],p[8],lb=p[4],ub=p[6])
        else:
            raise Exception('Syntax error in type! Cannot find matching format for SINCE')
            status = 'syntax_err'
    elif p[1] == 'O':
        if len(p)==3:
            p[0] = ONCE(p[2])
        elif len(p)==6:
            p[0] = ONCE(p[5],ub=p[3])
        elif len(p)==8:
            p[0] = ONCE(p[7],lb=p[3],ub=p[5])
        else:
            raise Exception('Syntax error in type! Cannot find matching format for ONCE')
            status = 'syntax_err'
    elif p[2] == '<->':
        p[0] = EQ(p[1],p[3])
    elif p[2] == '->':
        p[0] = IMPLY(p[1],p[3])
    elif p[1] == 'H':
        if len(p)==3:
            p[0] = HISTORICALLY(p[2])
        elif len(p)==6:
            p[0] = HISTORICALLY(p[5],ub=p[3])
        elif len(p)==8:
            p[0] = HISTORICALLY(p[7],lb=p[3],ub=p[5])
        else:
            raise Exception('Syntax error in type! Cannot find matching format for HISTORICALLY')
            status = 'syntax_err'

def p_paren_token(p):
    '''expression : LPAREN expression RPAREN'''
    p[0] = p[2]

def p_atomic_token(p):
    '''expression : ATOMIC'''
    p[0] = ATOM(p[1])
    # record_operators(p[0])

def p_bool_token(p):
    '''
    expression : TRUE
               | FALSE
    '''
    p[0] = BOOL(p[1])
    # if p[1] == 'TRUE':
    #     p[0] = BOOL('TRUE')
    # elif p[1] == 'FALSE':
    #     p[0] = BOOL('FALSE')

precedence = (
    ('left', 'SEMI'),
    ('left', 'COMMA'),
    ('left', 'AND', 'OR', 'IMPLY', 'EQ'),
    ('left', 'GLOBAL', 'FUTURE', 'UNTIL', 'RELEASE'),
    ('left', 'NEG','YESTERDAY','SINCE'),
    ('left', 'LPAREN', 'RPAREN','ATOMIC','LBRACK','RBRACK'),
)

# Error rule for syntax errors
def p_error(p):
    global status
    print("Syntax error in input!")
    print("Illegal character '%s'" % p.value[0])
    status = 'syntax_err'
    # sys.exit()

# Build the parser
parser = yacc.yacc()