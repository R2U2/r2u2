grammar MLTL;

// Grammar Rules

program
  : statement* EOF
  ;

statement
  : expr ';'
  | binding ';'
  ;

expr
  : op='!' expr         # prop_expr
  | expr op='&' expr    # prop_expr
  | expr op='|' expr    # prop_expr
  | expr op='<->' expr  # prop_expr
  | expr op='->' expr   # prop_expr
  | GLOBALLY '[' Number ']' expr                # ft_expr
  | GLOBALLY '[' Number ',' Number ']' expr     # ft_expr
  | FINALLY '[' Number ']' expr                 # ft_expr
  | FINALLY '[' Number ',' Number ']' expr      # ft_expr
  | expr UNTIL '[' Number ']' expr              # ft_expr
  | expr UNTIL '[' Number ',' Number ']' expr   # ft_expr
  | expr RELEASE '[' Number ']' expr            # ft_expr
  | expr RELEASE '[' Number ',' Number ']' expr # ft_expr
  | YESTERDAY expr                              # pt_expr
  | expr SINCE '[' Number ']' expr              # pt_expr
  | expr SINCE '[' Number ',' Number ']' expr   # pt_expr
  | ONCE '[' Number ']' expr                    # pt_expr
  | ONCE '[' Number ',' Number ']' expr         # pt_expr
  | HISTORICALLY expr                           # pt_expr
  | HISTORICALLY '[' Number ']' expr            # pt_expr
  | HISTORICALLY '[' Number ',' Number ']' expr # pt_expr
  | '(' expr ')' # parens_expr
  | Identifier   # atom_expr
  | 'TRUE'       # bool_expr
  | 'FALSE'      # bool_expr
  ;

binding
  : Identifier ':=' Filter '(' Identifier ')' Conditional Number
  | Identifier ':=' Filter '(' Identifier ',' Number ')' Conditional Number
  ;

// Lexical Spec

Filter
  : 'bool'
  | 'int'
  | 'float'
  | 'rate'
  | 'movavg'
  | 'abs_diff_angle'
  ;

Conditional : [!=><] '='? ;

GLOBALLY     : 'G' ;
FINALLY      : 'F' ;
UNTIL        : 'U' ;
RELEASE      : 'R' ;
YESTERDAY    : 'Y' ;
SINCE        : 'S' ;
ONCE         : 'O' ;
HISTORICALLY : 'H' ;

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
  : [a-zA-Z_]
  ;

Comment : '#' ~[\r\n]* -> skip;
WS  :  [ \t\r\n]+ -> skip;
