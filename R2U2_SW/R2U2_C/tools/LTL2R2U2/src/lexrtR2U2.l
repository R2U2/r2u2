%{

/*
SCANNER FOR the TP/FT/MPT/MFT part of the FPGA system
based on lexLTL.cc
*/

#include "y.tab.h"
#include "main.h"
#include <string.h>

%}
%option yylineno
%option noyywrap
%%
[\t \n]+       /*ignore whitespace and newlines */ ;

&&        { 
  /* normal default anyway */ 
    fprintf(stderr, "ERROR: Unrecognized symbol: %s\nTry &\n", yytext);
    exit(1);
}
\|\|        { 
  /* normal default anyway */ 
    fprintf(stderr, "ERROR: Unrecognized symbol: %s\nTry |\n", yytext);
    exit(1);
}
&  		{ return AND; }
\| 		{ return OR; }
!|~  		{ return NOT; }
-> 		{ return IMPLIES; }
\<-> 		{ return EQUIV; }

logic 		{ return LOGIC; }
const 		{ return CONST; }
map 		{ return MAP; }
lmap 		{ return LMAP; }
include 	{ return INCLUDE; }
atomic	 	{ return ATOMIC; }
pt 		{ return PT; }
ft 		{ return FT; }
\@		{ return LABELREF; }

X  		{ return NEXT; }
Y  		{ return PREV; }
U  		{ return UNTIL; }
R  		{ return RELEASE; }
S  		{ return SINCE; }
G  		{ return GLOBALLY; }
H  		{ return HISTORICALLY; }
F  		{ return FUTURE; }
O  		{ return ONCE; }
UP  		{ return UP; }
DOWN  		{ return DOWN; }


FALSE  		{ printf("false...\n");return FFALSE; }
TRUE   		{ printf("true...\n");return TTRUE; }

[A-Za-z][a-zA-Z_0-9]*   { 
  yylval.varName = (char *)malloc((strlen(yytext)+1)*sizeof(char));
  if (yylval.varName==NULL){ fprintf(stderr, "Memory error\n"); exit(1); }
  strcpy(yylval.varName, yytext);
  return PROP;
}

\"[^\"\r\n]*\"   { 
  		yylval.varName = strdup(yytext);
  		return STRING;
		}

[0-9]+   { 
	  int i;
          yylval.numval = 0;
          for (i=0; i<yyleng; i++) {
                     yylval.numval = 10 * yylval.numval + yytext[i] - '0';
                     }
  return NUMBER;
}

[0-9]+\.[0-9]+ { 
	  int i;
          yylval.floatval = atof(yytext);
  return FLOAT;
}

\( 		{ return LPAREN; }

\) 		{ return RPAREN; }

\%.*		{}
^#.*$		{}
--.*$		{}

.		{ return yytext[0]; }

<<EOF>>		{ if(yyin_save) {
			yyin = yyin_save;
			yyin_save=NULL;
			}
		  else {
			return yytext[0];
			}
		}

%%
/* 
FALSE | false  		{ printf("false...\n");return FFALSE; }
TRUE | true  		{ printf("true...\n");return TTRUE; }
*/
