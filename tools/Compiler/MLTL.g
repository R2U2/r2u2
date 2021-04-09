grammar MLTL;

// Grammar Rules

program : statement* EOF
        ;

statement : expr ';'
          | binding ';'
          ;

expr : op='!' expr         # prop_expr
     | expr op='&' expr    # prop_expr
     | expr op='|' expr    # prop_expr
     | expr op='<->' expr  # prop_expr
     | expr op='->' expr   # prop_expr
     | GLOBALLY '[' UnsignedInt ']' expr                # ft_expr
     | GLOBALLY '[' UnsignedInt ',' UnsignedInt ']' expr     # ft_expr
     | FINALLY '[' UnsignedInt ']' expr                 # ft_expr
     | FINALLY '[' UnsignedInt ',' UnsignedInt ']' expr      # ft_expr
     | expr UNTIL '[' UnsignedInt ']' expr              # ft_expr
     | expr UNTIL '[' UnsignedInt ',' UnsignedInt ']' expr   # ft_expr
     | expr RELEASE '[' UnsignedInt ']' expr            # ft_expr
     | expr RELEASE '[' UnsignedInt ',' UnsignedInt ']' expr # ft_expr
     | YESTERDAY expr                              # pt_expr
     | expr SINCE '[' UnsignedInt ']' expr              # pt_expr
     | expr SINCE '[' UnsignedInt ',' UnsignedInt ']' expr   # pt_expr
     | ONCE '[' UnsignedInt ']' expr                    # pt_expr
     | ONCE '[' UnsignedInt ',' UnsignedInt ']' expr         # pt_expr
     | HISTORICALLY expr                           # pt_expr
     | HISTORICALLY '[' UnsignedInt ']' expr            # pt_expr
     | HISTORICALLY '[' UnsignedInt ',' UnsignedInt ']' expr # pt_expr
     | '(' expr ')' # parens_expr
     | Identifier   # atom_expr
     | 'TRUE'       # bool_expr
     | 'FALSE'      # bool_expr
     ;

binding : Identifier ':=' Filter '(' Identifier ')' Conditional Number
        | Identifier ':=' Filter '(' Identifier ',' UnsignedInt ')' Conditional Number
        ;

// Lexical Spec

Filter : 'bool'
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

UnsignedInt : Digit+ ;

Number : '-'? Digit+ '.' Digit+
       | UnsignedInt
       ;

Identifier : Letter (Letter | Digit)* ;

fragment Digit :  [0-9] ;
fragment Letter : [a-zA-Z_] ;

Comment : '#' ~[\r\n]* -> skip;
WS  :  [ \t\r\n]+ -> skip;
