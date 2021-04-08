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
     | GLOBALLY '[' Natural ']' expr                # ft_expr
     | GLOBALLY '[' Natural ',' Natural ']' expr     # ft_expr
     | FINALLY '[' Natural ']' expr                 # ft_expr
     | FINALLY '[' Natural ',' Natural ']' expr      # ft_expr
     | expr UNTIL '[' Natural ']' expr              # ft_expr
     | expr UNTIL '[' Natural ',' Natural ']' expr   # ft_expr
     | expr RELEASE '[' Natural ']' expr            # ft_expr
     | expr RELEASE '[' Natural ',' Natural ']' expr # ft_expr
     | YESTERDAY expr                              # pt_expr
     | expr SINCE '[' Natural ']' expr              # pt_expr
     | expr SINCE '[' Natural ',' Natural ']' expr   # pt_expr
     | ONCE '[' Natural ']' expr                    # pt_expr
     | ONCE '[' Natural ',' Natural ']' expr         # pt_expr
     | HISTORICALLY expr                           # pt_expr
     | HISTORICALLY '[' Natural ']' expr            # pt_expr
     | HISTORICALLY '[' Natural ',' Natural ']' expr # pt_expr
     | '(' expr ')' # parens_expr
     | Identifier   # atom_expr
     | 'TRUE'       # bool_expr
     | 'FALSE'      # bool_expr
     ;

binding : Identifier ':=' Filter '(' Identifier ')' Conditional Number
        | Identifier ':=' Filter '(' Identifier ',' Natural ')' Conditional Number
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

Identifier : [a-zA-Z_] [a-zA-Z0-9_]* ;
Letter : [a-zA-Z_] ;
Natural :  [0-9]+ ;
Number : [+-]? [0-9]+ '.' [0-9]+ ;
Comment : '#' ~[\r\n]* -> skip;
WS  :  [ \t\r\n]+ -> skip;
