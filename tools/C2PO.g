//// Configuration Compiler for Property Observation (C2PO)

//// Parser Rules

grammar C2PO;

start: (struct_block | input_block | def_block | spec_block)* ;

struct_block: KW_STRUCT struct+ ;
struct: SYMBOL ':' '{' var_list+ '}' ';' ;

input_block: KW_INPUT var_list+ ;
var_list: SYMBOL (',' SYMBOL)* ':' type ';' ;

type: SYMBOL
    | SYMBOL '⟨' type '⟩'
    | SYMBOL REL_LT type REL_GT
    ;

def_block: KW_DEF def+ ;
def: SYMBOL '=' expr ';' ;

spec_block: KW_SPEC spec+ ;
spec: SYMBOL ':' contract ';'  
    | (SYMBOL ':')? expr ';' ;

contract: expr '=>' expr ;

expr: set_expr                  # SetExpr
    | SYMBOL '(' set_agg_binder (',' expr)? ')' '(' expr ')' # SetAggExpr
    | SYMBOL '(' expr_list? ')' # FuncExpr
    | expr '.' SYMBOL           # StructMemberExpr
    | ARITH_SUB expr            # UnaryExpr
    | ARITH_ADD expr            # UnaryExpr
    | BW_NEG expr               # UnaryExpr
    | LOG_NEG expr              # UnaryExpr
    | expr arith_mul_op expr    # ArithMulExpr
    | expr arith_add_op expr    # ArithAddExpr
    | expr BW_SHIFT_LEFT expr   # BWExpr
    | expr BW_SHIFT_RIGHT expr  # BWExpr
    | expr rel_ineq_op expr     # RelExpr
    | expr rel_eq_op expr       # RelExpr
    | expr BW_AND expr          # BWExpr
    | expr BW_XOR expr          # BWExpr
    | expr BW_OR expr           # BWExpr
    | expr tl_op expr           # TLBinExpr
    | tl_op expr                # TLUnaryExpr
    | expr LOG_XOR expr         # LogBinExpr
    | expr LOG_IMPL expr        # LogBinExpr
    | expr LOG_AND expr         # LogBinExpr
    | expr LOG_OR expr          # LogBinExpr
    | expr '?' expr ':' expr    # TernaryExpr
    | '(' expr ')'              # ParensExpr
    | literal                   # LiteralExpr
    ;

set_expr: SW_EMPTY_SET
        | '{' expr_list? '}'
        ;

set_agg_binder: SYMBOL ':' expr ;

interval: '[' INT (',' INT)? ']' ;

expr_list: expr (',' expr)* ;

tl_op: SYMBOL interval ;

literal: SYMBOL | INT | FLOAT ;

rel_eq_op: REL_EQ | REL_NEQ ;
rel_ineq_op: REL_GT | REL_LT | REL_GTE | REL_LTE  ;

arith_add_op: ARITH_ADD | ARITH_SUB ;
arith_mul_op: ARITH_MUL | ARITH_DIV | ARITH_MOD ;

unary_op: ARITH_SUB | BW_NEG ;

//// Lexical Spec

// Keywords
KW_STRUCT: 'STRUCT' ;
KW_INPUT: 'INPUT' ;
KW_DEF: 'DEFINE' ;
KW_SPEC: 'SPEC' ;

// Propositional logic ops/literals
LOG_NEG: '!' | '¬' ;
LOG_AND: '&&' | '∧' ;
LOG_OR: '||' | '∨' ;
LOG_XOR: 'XOR' | '⊕' ;
LOG_IMPL: '->' | '→' ;
LOG_IFF: '<->' | '↔' ;

// Bitwise ops
BW_NEG: '~' ;
BW_AND: '&'  ;
BW_OR: '|'  ;
BW_XOR: '^'  ;
BW_SHIFT_LEFT: '<<' ;
BW_SHIFT_RIGHT: '>>' ;

// Relational ops
REL_EQ: '==' ;
REL_NEQ: '!=' | '≠' ;
REL_GTE: '>=' | '≥' ;
REL_LTE: '<=' | '≤' ; 
REL_GT: '>' ;
REL_LT: '<' ;

// Arithmetic ops
ARITH_ADD: '+' ;
ARITH_SUB: '-' ;
ARITH_MUL: '*' | '•' | '⋅' ;
ARITH_DIV: '/' | '÷' ;
ARITH_MOD: '%' ;
ARITH_POW: '**' ;
ARITH_SQRT: '√' ;
ARITH_PM: '+/-' | '±' ;

// Set-wise ops
SW_EMPTY_SET: '∅' ;
SW_MEMBER: '∈' ;
SW_SUBSET: '⊂' ;
SW_SUBSETEQ: '⊆' ;
SW_SUM: '∑' ;
SW_PROD: '∏' ;
SW_UNION: '⋃' ;
SW_INTERSECTION: '⋂' ;
SW_AND: '⋀' ;
SW_OR: '⋁' ;
SW_CTPROD: '×' ; 

SYMBOL
  : LETTER (LETTER | DIGIT)*
  ;

FLOAT
  : SIGN? DIGIT+ '.' DIGIT+
  ;

INT
  : SIGN? NONZERODIGIT DIGIT*
  | '0'
  ;

fragment
SIGN
  : [-]
  ;

fragment
DIGIT
  :  [0-9]
  ;

fragment
NONZERODIGIT
  : [1-9]
  ;

fragment
LETTER
  : [a-zA-Z_]
  ;

COMMENT : '--' ~[\r\n]* -> skip;
WS  :  [ \t\r\n]+ -> channel(HIDDEN);
