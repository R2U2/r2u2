//// Configuration Compiler for Property Observation -- C2PO
//// Configuration Compiler for Property Organization -- C2PO
//// Configuration Compiler for Proposition Organization -- C2PO
//// Compiler for Creation and Coordination of Configurations for Proposition Organization -- C4PO

//// Parser Rules

grammar C2PO;

start: (var_block | def_block | spec_block)* ;

var_block: KW_VAR var_list+ order_list ;
var_list: IDENTIFIER (',' IDENTIFIER)* ':' type ';' ;
order_list: KW_ORDER ':' IDENTIFIER (',' IDENTIFIER)* ';' ;

type: BASE_TYPE
    | KW_SET set_param
    ;

set_param: '⟨' BASE_TYPE '⟩'
         | REL_LT BASE_TYPE REL_GT
         ;

def_block: KW_DEF def_list+ ;
def_list: IDENTIFIER '=' expr ';' ;

spec_block: KW_SPEC spec+ ;
spec: (IDENTIFIER ':')? expr ';' ;

expr: expr '?' expr ':' expr        # TernaryExpr
    | expr LOG_OR expr              # LogBinExpr
    | expr LOG_XOR expr             # LogBinExpr
    | expr LOG_AND expr             # LogBinExpr
    | expr LOG_IMPL expr            # LogBinExpr
    // | expr BW_OR expr               # BWBinExpr
    // | expr BW_XOR expr              # BWBinExpr
    // | expr BW_AND expr              # BWBinExpr
    | expr tl_bin_op interval expr  # TLBinExpr
    | tl_unary_op interval expr     # TLUnaryExpr
    | expr rel_eq_op expr           # RelExpr
    | expr rel_ineq_op expr         # RelExpr
    | expr arith_add_op expr        # ArithAddExpr
    | expr arith_mul_op expr        # ArithMulExpr
    | unary_op expr                 # UnaryExpr
    | IDENTIFIER '(' expr ')'       # FunExpr
    | set_expr                      # SetExpr
    | '(' expr ')'                  # ParensExpr
    | log_lit                       # LitExpr
    | IDENTIFIER                    # LitExpr
    | INT                           # LitExpr
    | FLOAT                         # LitExpr
    ;

set_expr: SW_EMPTY_SET
        | '{' '}'
        | '{' IDENTIFIER (',' IDENTIFIER)* '}'
        ;

interval: '[' INT (',' INT)? ']' ;

log_lit: TRUE | FALSE ;
unary_op: LOG_NEG | ARITH_SUB ; // | BW_NEG ;
tl_unary_op: TL_GLOBAL | TL_FUTURE | TL_HISTORICAL | TL_ONCE ;
tl_bin_op: TL_UNTIL | TL_RELEASE | TL_SINCE ;
rel_eq_op: REL_EQ | REL_NEQ ;
rel_ineq_op: REL_GT | REL_LT | REL_GTE | REL_LTE  ;
arith_add_op: ARITH_ADD | ARITH_SUB ;
arith_mul_op: ARITH_MUL | ARITH_DIV | ARITH_MOD ;

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
BW_AND: '&' ;
BW_OR: '|' ;
BW_XOR: '^' ;

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
SW_SUPSET: '⊃' ;
SW_SUPSETEQ: '⊇' ;
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
  : [+-]
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

COMMENT : '#' ~[\r\n]* -> skip;
WS  :  [ \t\r\n]+ -> channel(HIDDEN);
