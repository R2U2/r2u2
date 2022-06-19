grammar MLTL;

// Grammar Rules

program
  : block* EOF
  ;

block
  : var_block
  | def_block
  | spec_block
  | order_block
  ;

var_block
  : VAR_KW var_statement+
  ;

var_statement
  : Identifier (',' Identifier)* ':' type ';'
  ;

def_block
  : DEF_KW def_statement+
  ;

def_statement
  : Identifier '=' expr ';'
  ;

spec_block
  : SPEC_KW spec_statement
  ;

spec_statement
  : (Identifier ':')? boolean_expr ';'
  ;

order_block
  : ORDER_KW Identifier (',' Identifier)* ';'
  ;

// contract
//   : (formulaIdentifier ':')? expr '=>' expr
//   ;

boolean_expr
  : UnaryTemporalOp '[' Integer ']' boolean_expr                   # UnaryTemporalExpr
  | UnaryTemporalOp '[' Integer ',' Integer ']' boolean_expr       # UnaryTemporalExpr
  | boolean_expr BinaryTemporalOp '[' Integer ']' boolean_expr             # BinaryTemporalExpr
  | boolean_expr BinaryTemporalOp '[' Integer ',' Integer ']' boolean_expr # BinaryTemporalExpr
  | op='!' boolean_expr         # PropExpr
  | boolean_expr op='&' boolean_expr    # PropExpr
  | boolean_expr op='|' boolean_expr    # PropExpr
  | boolean_expr op='<->' boolean_expr  # PropExpr
  | boolean_expr op='->' boolean_expr   # PropExpr
  | '(' boolean_expr ')'        # ParensExpr
  | Identifier    # AtomExpr
  | TRUE_KW       # BoolExpr
  | FALSE_KW      # BoolExpr
  ;

type
  : BaseType
  | SET_KW '<' BaseType '>'
  ;


// Lexical Spec

Conditional : [!=><] '='? ;

BaseType
  : BOOL_KW
  | INT_KW
  | FLOAT_KW
  ;

VAR_KW : 'VAR';
DEF_KW : 'DEF';
SPEC_KW : 'SPEC';
ORDER_KW : 'ORDER';
BOOL_KW : 'bool';
INT_KW : 'int';
FLOAT_KW : 'float';
SET_KW : 'set';
TRUE_KW : 'TRUE';
FALSE_KW : 'FALSE';

UnaryTemporalOp
  : 'G'
  | 'F'
  | 'O'
  | 'H'
  ;

BinaryTemporalOp
  : 'U'
  | 'R'
  | 'Y'
  | 'S'
  ;

LiteralIdentifier : 'a' Digit+;
LiteralSignalIdentifier : 's' Digit+;

Identifier
  : Letter (Letter | Digit)*
  ;

Number
  : Integer
  | Float
  ;

Integer
  : Sign? NonzeroDigit Digit*
  | '0'
  ;

Float
  : Sign? Digit+ '.' Digit+
  ;

fragment
Sign
  : [+-]
  ;

fragment
Digit
  :  [0-9]
  ;

fragment
NonzeroDigit
  : [1-9]
  ;

fragment
Letter
  : [a-zA-Z_]
  ;

Comment : '#' ~[\r\n]* -> skip;
WS  :  [ \t\r\n]+ -> skip;
