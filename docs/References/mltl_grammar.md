# MLTL Grammar

```
expression  : expression AND expression
            | expression OR expression
            | NEG expression
            | GLOBAL LBRACK NUMBER RBRACK expression
            | GLOBAL LBRACK NUMBER COMMA NUMBER RBRACK expression
            | FUTURE LBRACK NUMBER RBRACK expression
            | FUTURE LBRACK NUMBER COMMA NUMBER RBRACK expression
            | expression UNTIL LBRACK NUMBER RBRACK expression
            | expression UNTIL LBRACK NUMBER COMMA NUMBER RBRACK expression
            | expression WEAK_UNTIL LBRACK NUMBER RBRACK expression
            | expression WEAK_UNTIL LBRACK NUMBER COMMA NUMBER RBRACK expression
```

```
precedence = (
    ('left', 'AND', 'OR'),
    ('left', 'GLOBAL', 'FUTURE', 'UNTIL','WEAK_UNTIL'), 
    ('left', 'NEG'),
    ('left', 'LPAREN', 'RPAREN','ATOMIC','LBRACK','RBRACK'),
)
```

For more details on operator definitions, see {footcite:p}`AJR2025` and {footcite:p}`KZJZR20`. 

:::{footbibliography}
:::
