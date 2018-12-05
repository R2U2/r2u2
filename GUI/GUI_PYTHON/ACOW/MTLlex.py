# ------------------------------------------------------------
# MTLlex.py
#
# tokenizer for a simple expression evaluator for
# numbers and G,&,!,U,(),[]
# ------------------------------------------------------------
import ply.lex as lex
#import ply.yacc as yacc

reserved = {
	'G' : 'GLOBAL',
	'U' : 'UNTIL',
	'W' : 'WEAK_UNTIL',
	'F' : 'FUTURE',
	# '!' : 'NOT',
	# '&' : 'AND',
}

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
	'ATOMIC'#atomic
        ]+ list(reserved.values())


# Regular statement rules for tokens.
# t_GLOBAL 		= r'G'
# t_UNTIL		= r'U'
t_AND			= r'\&'
t_OR			= r'\|'
t_NEG			= r'\!'
#t_ATOMIC		= r'([A-Za-z])\w*'
t_COMMA			= r','
t_LPAREN		= r'\('
t_RPAREN		= r'\)'
t_LBRACK		= r'\['
t_RBRACK		= r'\]'

def t_NUMBER(t):
	r'\d+'
	t.value = int(t.value)    
	return t

def t_ATOMIC(t):
	r'([A-Za-z])\w*'
	if t.value in reserved:
		t.type = reserved[t.value]
	return t

def t_COMMENT(t):
	r'\#.*'
	pass

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t\n'

# Error handling rule
def t_error(t):
	print("Illegal character '%s'" % t.value[0])
	t.lexer.skip(1)

lexer = lex.lex()
