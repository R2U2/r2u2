grammar MLTL;

// Grammar Rules

program
  : (statement? ';')* EOF
  ;

statement
  : (formulaIdentifier ':')? expr
  | contract
  | binding
  | mapping
  | setAssignment
  ;

contract
  : (formulaIdentifier ':')? expr '=>' expr
  ;

expr
  : UnaryTemporalOp '[' Number ']' expr                   # UnaryTemporalExpr
  | UnaryTemporalOp '[' Number ',' Number ']' expr        # UnaryTemporalExpr
  | expr BinaryTemporalOp '[' Number ']' expr             # BinaryTemporalExpr
  | expr BinaryTemporalOp '[' Number ',' Number ']' expr  # BinaryTemporalExpr
  | op='!' expr         # PropExpr
  | expr op='&' expr    # PropExpr
  | expr op='|' expr    # PropExpr
  | expr op='<->' expr  # PropExpr
  | expr op='->' expr   # PropExpr
  | '(' expr ')'        # ParensExpr
  | atomicIdentifier    # AtomExpr
  | 'TRUE'       # BoolExpr
  | 'FALSE'      # BoolExpr
  ;

binding
  : atomicIdentifier '=' filterIdentifier '(' filterArgument (',' filterArgument)* ')' Conditional (Number | signalIdentifier)
  ;

mapping
  : signalIdentifier '=' Number
  ;

setAssignment
  : setIdentifier '=' '{' atomicIdentifier (',' atomicIdentifier)* '}'
  ;

filterArgument
  : LiteralSignalIdentifier
  | Identifier
  | Number
  ;

formulaIdentifier : Identifier;
setIdentifier : Identifier;
filterIdentifier : Identifier;
atomicIdentifier : LiteralAtomicIdentifier | Identifier;
signalIdentifier : LiteralSignalIdentifier | Identifier;

// Lexical Spec

Conditional : [!=><] '='? ;

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

LiteralAtomicIdentifier : 'a' Digit+;
LiteralSignalIdentifier : 's' Digit+;

Identifier
  : Letter (Letter | Digit)*
  ;

Number
  : Integer
  | Float
  ;

fragment
Integer
  : Sign? NonzeroDigit Digit*
  | '0'
  ;

fragment
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
  : [a-zA-Z_\-]
  ;

Comment : '#' ~[\r\n]* -> skip;
WS  :  [ \t\r\n]+ -> skip;
