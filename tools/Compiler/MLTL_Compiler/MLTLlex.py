# ------------------------------------------------------------
# TLlex.py
#
# tokenizer for a simple expression evaluator for
# numbers and G,&,~,|,U,(),[]
# Reference: https://www.dabeaz.com/ply/ply.html#ply_nn9
# ------------------------------------------------------------
import ply.lex as lex
#import ply.yacc as yacc

literal_names = {}
for literal in ['TRUE', 'FALSE']:
    literal_names.update({getattr(literal, x)() : literal for x in ['upper', 'title', 'lower']})
    # literal_names.update({getattr(literal[0], x)() : literal for x in ['upper', 'lower']})


reserved = {
# future time
    'G' : 'GLOBAL',
    'U' : 'UNTIL',
    'R' : 'RELEASE',
    'F' : 'FUTURE',
# past time
    'Y' : 'YESTERDAY',
    'S' : 'SINCE', #can be unbounded or bounded
    'O' : 'ONCE', #can be unbounded or bounded
    'H' : 'HISTORICALLY', #can be unbounded or bounded

    # '!' : 'NOT',
    # '&' : 'AND',
    'TRUE' : 'TRUE',
    'FALSE' : 'FALSE',

}

reserved.update(literal_names)
#print(reserved)
#print(list(set(reserved.values())))
# List of token names. This is compulsory.
tokens = [
    'NUMBER',
    'COMMA',
    'LPAREN',
    'RPAREN',
    'LBRACK',
    'RBRACK',
    'AND',
    'OR',
    'NEG',
    'IMPLY',
    'EQ',
    'ATOMIC',
    'SEMI',
        ]+ list(set(reserved.values()))


# Regular statement rules for tokens.
# t_GLOBAL      = r'G'
# t_UNTIL       = r'U'
t_AND           = r'\&'
t_OR            = r'\|'
t_NEG           = r'\!'
t_IMPLY         = r'->'
t_EQ            = r'<->'
t_COMMA         = r','
t_LPAREN        = r'\('
t_RPAREN        = r'\)'
t_LBRACK        = r'\['
t_RBRACK        = r'\]'

def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t

def t_ATOMIC(t):
    r'([A-Za-z])\w*'
    if t.value in reserved:
        t.type = reserved[t.value]

#    if t.value in literal_names.keys():
#        t.type = literal_names[t.value]
#        t.value = t.type
    return t

def t_SEMI(t):
    r';'
    t.value = t.lexer.lineno
    return t

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_COMMENT(t):
    r'\#.*'
    pass

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'

# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

lexer = lex.lex()

# print of lex token
# lexer.input("""a0;
#     a1&a3;""")
# while True:
#     tok = lexer.token()
#     if not tok:
#        break
#     print(tok)
