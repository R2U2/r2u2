/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_YACCRTR2U2_TAB_H_INCLUDED
# define YY_YY_YACCRTR2U2_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    AND = 258,
    OR = 259,
    NOT = 260,
    IMPLIES = 261,
    NEXT = 262,
    PREV = 263,
    SINCE = 264,
    UNTIL = 265,
    GLOBALLY = 266,
    LPAREN = 267,
    RPAREN = 268,
    RELEASE = 269,
    EQUIV = 270,
    UP = 271,
    DOWN = 272,
    CONST = 273,
    MAP = 274,
    LMAP = 275,
    LOGIC = 276,
    INCLUDE = 277,
    ATOMIC = 278,
    PT = 279,
    FT = 280,
    ONCE = 281,
    HISTORICALLY = 282,
    PROP = 283,
    STRING = 284,
    FFALSE = 285,
    TTRUE = 286,
    NUMBER = 287,
    FLOAT = 288,
    FUTURE = 289,
    LABELREF = 290
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 69 "yaccrtR2U2.y" /* yacc.c:1909  */

    struct node *nPtr;		/* node pointer */
    char *varName;              /* name of a variable */
    int numval;
    int floatval;
    struct {int lb; int ub;} intvl;

#line 98 "yaccrtR2U2.tab.h" /* yacc.c:1909  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_YACCRTR2U2_TAB_H_INCLUDED  */
