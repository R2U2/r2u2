# ------------------------------------------------------------
# MLTLparse.py
#
# Parser for MTL formula.
# Construct observer abstract syntax tree
# Syntax : https://ti.arc.nasa.gov/m/profile/kyrozier/PANDA/PANDA.html
# ------------------------------------------------------------
import ply.yacc as yacc
from .MLTLlex import tokens
from .Observer import *
import sys

__all__ = ['cnt2observer', 'parser']

operator_cnt = 0
cnt2observer = {}

def record_operators(ob):
	global operator_cnt
	cnt2observer[operator_cnt] = ob
	operator_cnt += 1

def p_MLTL_operators(p):
	'''
	expression 	: expression AND expression
				| NEG expression
				| NEXT expression
				| expression OR expression
				| FUTURE LBRACK NUMBER RBRACK expression
				| FUTURE LBRACK NUMBER COMMA NUMBER RBRACK expression
				| GLOBAL LBRACK NUMBER RBRACK expression
				| GLOBAL LBRACK NUMBER COMMA NUMBER RBRACK expression
				| expression UNTIL LBRACK NUMBER RBRACK expression
				| expression UNTIL LBRACK NUMBER COMMA NUMBER RBRACK expression
	'''
	if p[1] == '!':
		p[0] = NEG(p[2])
	elif p[1] == 'X':
		p[0] = GLOBAL(p[2],lb=1,ub=1)
	elif len(p)>2 and p[2] == '&':
	 	p[0] = AND(p[1],p[3])
	elif len(p)>2 and p[2] == '|':
	 	p[0] = NEG(AND(NEG(p[1]),NEG(p[3])))
	 	# p[0] = OR(p[1],p[3])
	elif p[1] == 'G' and len(p) == 6:
		p[0] = GLOBAL(p[5],ub=p[3])
	elif p[1] == 'G' and len(p)==8:
		p[0] = GLOBAL(p[7],lb=p[3],ub=p[5])
	elif p[2] == 'U' and len(p)==7:
		p[0] = UNTIL(p[1],p[6],ub=p[4])
	elif p[2] == 'U' and len(p)==9:
		p[0] = UNTIL(p[1],p[8],lb=p[4],ub=p[6])
	elif p[1] == 'F' and len(p)==6:
		p[0] = UNTIL(BOOL('TRUE'),p[5],ub=p[3])
	elif p[1] == 'F' and len(p)==8:
		p[0] = UNTIL(BOOL('TRUE'),p[7],lb=p[3],ub=p[5])

	else:
		raise Exception('Syntax error in type! Cannot find matching format.')
		sys.exit(0)
	record_operators(p[0])

def p_paren_token(p):
	'''expression : LPAREN expression RPAREN'''
	p[0] = p[2]

def p_atomic_token(p):
	'''expression : ATOMIC'''
	p[0] = ATOM(p[1])
	record_operators(p[0])

def p_bool_token(p):
	'''
	expression : TRUE
				| FALSE
	'''
	if p[1] == 'TRUE':
		p[0] = BOOL('TRUE')
	elif p[1] == 'FALSE':
		p[0] = BOOL('FALSE')

precedence = (
	('left', 'AND', 'OR'),
	('left', 'GLOBAL', 'UNTIL'),
	('left', 'NEG','NEXT'),
	('left', 'LPAREN', 'RPAREN','ATOMIC','LBRACK','RBRACK'),
)

# Error rule for syntax errors
def p_error(p):
	print("Syntax error in input!")
	sys.exit()

# Build the parser
parser = yacc.yacc()