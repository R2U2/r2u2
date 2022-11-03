//// Configuration Compiler for Property Observation (C2PO)

//// Parser Rules

grammar C2PO;

start: (var_block | def_block | spec_block)* ;

var_block: KW_VAR var_list+ order_list ;
var_list: IDENTIFIER (',' IDENTIFIER)* ':' type ';' ;
order_list: KW_ORDER ':' IDENTIFIER (',' IDENTIFIER)* ';' ;

type: BASE_TYPE
    | KW_SET '⟨' type '⟩'
    | KW_SET REL_LT type REL_GT
    ;

def_block: KW_DEF def+ ;
def: IDENTIFIER '=' expr ';' ;

spec_block: KW_SPEC spec+ ;
spec: IDENTIFIER ':' contract ';'  
    | (IDENTIFIER ':')? expr ';' ;

contract: expr '=>' expr ;

expr: set_expr                  # SetExpr
    | IDENTIFIER '(' expr_list? ')' # FuncExpr
    | ARITH_SUB expr            # UnaryExpr
    | ARITH_ADD expr            # UnaryExpr
    | BW_NEG expr               # UnaryExpr
    | expr arith_mul_op expr    # ArithMulExpr
    | expr arith_add_op expr    # ArithAddExpr
    | expr BW_SHIFT_LEFT expr   # BWExpr
    | expr BW_SHIFT_RIGHT expr  # BWExpr
    | expr rel_ineq_op expr     # RelExpr
    | expr rel_eq_op expr       # RelExpr
    | expr BW_AND expr          # BWExpr
    | expr BW_XOR expr          # BWExpr
    | expr BW_OR expr           # BWExpr
    | expr tl_bin_op expr       # TLBinExpr
    | tl_unary_op expr          # TLUnaryExpr
    | expr LOG_AND expr         # LogBinExpr
    | expr LOG_OR expr          # LogBinExpr
    | expr '?' expr ':' expr    # TernaryExpr
    | '(' expr ')'              # ParensExpr
    | literal                   # LiteralExpr
    ;

set_expr: SW_EMPTY_SET
        | '{' expr_list? '}'
        ;

interval: '[' INT (',' INT)? ']' ;

expr_list: expr (',' expr)* ;

tl_unary_op: (TL_GLOBAL | TL_FUTURE | TL_HISTORICAL | TL_ONCE) interval ;
tl_bin_op: (TL_UNTIL | TL_RELEASE | TL_SINCE) interval ;

literal: TRUE | FALSE | IDENTIFIER | INT | FLOAT ;

rel_eq_op: REL_EQ | REL_NEQ ;
rel_ineq_op: REL_GT | REL_LT | REL_GTE | REL_LTE  ;

arith_add_op: ARITH_ADD | ARITH_SUB ;
arith_mul_op: ARITH_MUL | ARITH_DIV | ARITH_MOD ;

unary_op: ARITH_SUB | BW_NEG ;

//// Lexical Spec

// Types
BASE_TYPE: 'bool'
         | 'int'
         | 'float'
         ;

// Keywords
KW_VAR: 'VAR' ;
KW_DEF: 'DEFINE' ;
KW_SPEC: 'SPEC' ;
KW_ORDER: 'Order' ;
KW_SET: 'set' ;

// Propositional logic ops/literals
LOG_NEG: '!' | '¬' ;
LOG_AND: '&&' | '∧' ;
LOG_OR: '||' | '∨' ;
LOG_XOR: 'XOR' | '⊕' ;
LOG_IMPL: '->' | '→' ;
LOG_IFF: '<->' | '↔' ;
TRUE: 'TRUE' | 'true' | '⊤' ;
FALSE: 'FALSE' | 'false' | '⊥' ;

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

// Temporal ops
TL_GLOBAL: 'G' | '𝓖' | '□' ;
TL_FUTURE: 'F' | '𝓕' | '⋄' | '♢' | '◊' ;
TL_NEXT: 'X' | '○' ;
TL_SINCE: 'S' | '𝓢' ;
TL_ONCE: 'O' | '𝓞' ;
TL_UNTIL: 'U' | '𝓤' ;
TL_RELEASE: 'R' | '𝓡' ;  
TL_HISTORICAL: 'H' | '𝓗' ;

// First-order -- not used
FO_FORALL: 'FORALL' | '∀' ;
FO_EXISTS: 'EXISTS' | '∃' ;

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

IDENTIFIER
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
