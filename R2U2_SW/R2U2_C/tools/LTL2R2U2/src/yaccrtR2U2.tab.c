/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 1 "yaccrtR2U2.y" /* yacc.c:339  */


/*
based on yaccLTL.cc
K.Y.Rozier
June, 2011
*/

/* This is a parser for LTL formulas in in-fix order */

#include "main.h"

#define NYI printf("JSC: NYI\n");


int yylex(); /*to make g++ shut up*/
int yywhere();

extern FILE *yyin;

/*********************************************************
	yyerror
*********************************************************/
#ifdef FOO
int yyerror(const char *s){
extern int yynerrs;
static int list = 0;
if (!list) {
  printf("[error %d] ",yynerrs+1); yywhere();
  if (list=s[strlen(s)-1]==':') fputs(s,stdout);
    else puts(s);
  } else if (*s!='\n') putchar(' '),fputs(s,stdout);
    else putchar('\n'),list=0;
}
#endif

extern int yylineno;

 int yyerror(const char *msg) { /*to make g++ shut up*/
    (void) fprintf(stderr, "Error near line %d: %s\n", yylineno, msg);
     return (0);
 } /*end yyerror*/

/*********************************************************
	Variable declarations
*********************************************************/
 struct node *current;
 struct node *current2;
 struct node *current_op1;
 struct node *current_op2;
 struct node *current_op3;
 int i;

 KItem search;            /*a variable name to search for*/
 int used;                /*did we use this var already?*/

extern FILE *yyin_save;
FILE *f;

extern t_logic thelogic;
extern int fix_ft_not;

/*for parsing the formula string*/
#undef YY_INPUT
#define YY_INPUT(b, r, ms) (r = my_yyinput(b, me))


#line 134 "yaccrtR2U2.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "yaccrtR2U2.tab.h".  */
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
#line 69 "yaccrtR2U2.y" /* yacc.c:355  */

    struct node *nPtr;		/* node pointer */
    char *varName;              /* name of a variable */
    int numval;
    int floatval;
    struct {int lb; int ub;} intvl;

#line 218 "yaccrtR2U2.tab.c" /* yacc.c:355  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_YACCRTR2U2_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 233 "yaccrtR2U2.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  39
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   133

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  42
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  7
/* YYNRULES -- Number of rules.  */
#define YYNRULES  36
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  80

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   290

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,    41,     2,    34,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    35,     2,
       2,    38,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    39,     2,    40,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    36,
      37
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   126,   126,   145,   149,   162,   193,   202,   219,   238,
     239,   250,   250,   290,   323,   353,   372,   390,   441,   466,
     492,   519,   544,   581,   618,   648,   683,   706,   889,  1029,
    1058,  1091,  1263,  1297,  1312,  1321,  1330
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "AND", "OR", "NOT", "IMPLIES", "NEXT",
  "PREV", "SINCE", "UNTIL", "GLOBALLY", "LPAREN", "RPAREN", "RELEASE",
  "EQUIV", "UP", "DOWN", "CONST", "MAP", "LMAP", "LOGIC", "INCLUDE",
  "ATOMIC", "PT", "FT", "ONCE", "HISTORICALLY", "PROP", "STRING", "FFALSE",
  "TTRUE", "NUMBER", "FLOAT", "'.'", "':'", "FUTURE", "LABELREF", "'='",
  "'['", "']'", "','", "$accept", "input", "formula_stmt", "logicID",
  "formula", "@1", "interval", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,    46,    58,   289,   290,    61,    91,
      93,    44
};
# endif

#define YYPACT_NINF -37

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-37)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int8 yypact[] =
{
      62,    89,    89,    89,   -36,    89,    89,    89,   -19,    -5,
      16,     6,   -36,   -36,    10,   -37,   -37,   -36,    11,    52,
      20,    47,   -37,   -37,   -37,    27,    89,     4,   -37,   -37,
      17,    22,   -13,    29,    89,    89,   -37,    89,   -37,   -37,
      62,    89,    89,    89,   -36,   -36,   -36,    89,   -10,   -37,
     -37,    36,    39,   -37,   -37,    59,   -37,   -37,   -37,    89,
     -37,   -37,   -37,    72,    40,    89,    89,    89,    18,   -37,
      44,   -37,   -37,   -37,   -37,   108,    23,   118,    37,   -37
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     0,    34,     0,     0,     0,     0,     0,
       0,     0,    34,    34,    13,    16,    15,    34,     0,     0,
       0,     5,    17,    20,    21,     0,     0,     0,    18,    19,
       0,     0,     0,     0,     0,     0,    11,     0,    14,     1,
       3,     0,     0,     0,    34,    34,    34,     0,     0,    22,
      33,     0,     0,     9,    10,     0,     2,    25,    23,     0,
      24,     4,    26,    27,    28,     0,     0,     0,    29,    35,
       0,     7,     8,     6,    12,    32,    30,    31,     0,    36
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
     -37,    45,   -37,   -37,    -1,   -37,     3
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
      -1,    19,    20,    55,    21,    59,    26
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      22,    23,    24,    25,    27,    28,    29,    41,    42,    30,
      43,    53,    54,    44,    45,    34,    35,    50,    46,    47,
      37,    41,    42,    31,    43,    49,    41,    42,    32,    43,
      69,    70,    44,    57,    58,    33,    60,    46,    47,    38,
      62,    63,    64,    41,    42,    36,    68,    65,    66,    67,
      41,    42,    39,    43,    40,    51,    44,    45,    74,    48,
      52,    46,    47,    56,    75,    76,    77,     1,    71,     2,
       3,    72,    73,     4,     5,    41,    78,    79,     6,     7,
       0,     8,     9,    10,    11,    61,     0,     0,    12,    13,
      14,     0,    15,    16,     1,     0,     2,     3,    17,    18,
       4,     5,     0,     0,     0,     6,     7,     0,     0,     0,
       0,    41,    42,     0,    43,    12,    13,    14,     0,    15,
      16,    41,    42,    47,    43,    17,    18,    44,     0,     0,
       0,     0,     0,    47
};

static const yytype_int8 yycheck[] =
{
       1,     2,     3,    39,     5,     6,     7,     3,     4,    28,
       6,    24,    25,     9,    10,    12,    13,    13,    14,    15,
      17,     3,     4,    28,     6,    26,     3,     4,    12,     6,
      40,    41,     9,    34,    35,    29,    37,    14,    15,    28,
      41,    42,    43,     3,     4,    35,    47,    44,    45,    46,
       3,     4,     0,     6,    34,    38,     9,    10,    59,    32,
      38,    14,    15,    34,    65,    66,    67,     5,    32,     7,
       8,    32,    13,    11,    12,     3,    32,    40,    16,    17,
      -1,    19,    20,    21,    22,    40,    -1,    -1,    26,    27,
      28,    -1,    30,    31,     5,    -1,     7,     8,    36,    37,
      11,    12,    -1,    -1,    -1,    16,    17,    -1,    -1,    -1,
      -1,     3,     4,    -1,     6,    26,    27,    28,    -1,    30,
      31,     3,     4,    15,     6,    36,    37,     9,    -1,    -1,
      -1,    -1,    -1,    15
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     5,     7,     8,    11,    12,    16,    17,    19,    20,
      21,    22,    26,    27,    28,    30,    31,    36,    37,    43,
      44,    46,    46,    46,    46,    39,    48,    46,    46,    46,
      28,    28,    12,    29,    48,    48,    35,    48,    28,     0,
      34,     3,     4,     6,     9,    10,    14,    15,    32,    46,
      13,    38,    38,    24,    25,    45,    34,    46,    46,    47,
      46,    43,    46,    46,    46,    48,    48,    48,    46,    40,
      41,    32,    32,    13,    46,    46,    46,    46,    32,    40
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    42,    43,    43,    43,    44,    44,    44,    44,    45,
      45,    47,    46,    46,    46,    46,    46,    46,    46,    46,
      46,    46,    46,    46,    46,    46,    46,    46,    46,    46,
      46,    46,    46,    46,    48,    48,    48
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     3,     2,     3,     1,     4,     4,     4,     1,
       1,     0,     4,     1,     2,     1,     1,     2,     2,     2,
       2,     2,     3,     3,     3,     3,     3,     3,     3,     3,
       4,     4,     4,     3,     0,     3,     5
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 127 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
// NYI: http://flex.sourceforge.net/manual/Multiple-Input-Buffers.html#Multiple-Input-Buffers
	yyerror("NYI");
	if (yyin_save){
		yyerror("No include files");
		}

		// remove ".."
	yylval.varName[strlen(yylval.varName)-1] = '\0';
	
	if(!(f = fopen(yylval.varName+1,"r"))){
		yyerror("Cannot open include file");
		}

	yyin_save = yyin;
	yyin = f;
	}
#line 1383 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 146 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
	DEB(printf("SINGLE FSTMT: %x %d\n",(yyvsp[-1].nPtr),((yyvsp[-1].nPtr))?(yyvsp[-1].nPtr)->num:-1));
	}
#line 1391 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 150 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
	DEB(printf("FSTMT: %x %d     ",(yyvsp[-2].nPtr),((yyvsp[-2].nPtr))?(yyvsp[-2].nPtr)->num:-1));
	DEB(printf("INPUT: %x %d\n",(yyvsp[0].nPtr),((yyvsp[0].nPtr))?(yyvsp[0].nPtr)->num:-1));
	}
#line 1400 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 162 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); 
			}
	    	current->me = strdup("end");
    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;
    		current->thelogic = thelogic;
        	current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->op = OPC_END_SEQUENCE;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
	    	rtR2U2_print(&fp, current);

		// Label for default formula
		DEB(printf("Label: %s: %3.3d\n", "DEFAULT" ,(yyvsp[0].nPtr)->num+1););
		rtR2U2_print_label(&fp, 
			(yyvsp[0].nPtr)->thelogic?"ftDEFAULT":"ptDEFAULT", 
			(yyvsp[0].nPtr)->num+1,
			(yyvsp[0].nPtr)->thelogic,
			-1);

    		(yyval.nPtr) = (yyvsp[0].nPtr);
		}
#line 1432 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 194 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
		printf("logic set to: %d\n", thelogic);
		(yyval.nPtr) = NULL;
		}
#line 1441 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 203 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		search.setName((yyvsp[-2].varName));
    		if (varList.query(search)){
			printf("Error: %s redefined\n", (yyvsp[-2].varName));
			}
    		else {
			printf("MAP:variable %s added with index %d\n",(yyvsp[-2].varName),(yyvsp[0].numval));
			search.setInfo((yyvsp[0].numval));
			varList.addItem(search);
    			} 
		(yyval.nPtr) = NULL;
    		}
#line 1458 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 220 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		search.setName((yyvsp[-2].varName));
    		if (labelList.query(search)){
			printf("Error: %s redefined\n", (yyvsp[-2].varName));
			}
    		else {
			printf("MAP:label %s added with index %d\n",(yyvsp[-2].varName),(yyvsp[0].numval));
			search.setInfo((yyvsp[0].numval));
			labelList.addItem(search);
    			} 
		(yyval.nPtr) = NULL;
    		}
#line 1475 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 238 "yaccrtR2U2.y" /* yacc.c:1646  */
    {thelogic = ptLTL;}
#line 1481 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 239 "yaccrtR2U2.y" /* yacc.c:1646  */
    {thelogic = ftLTL;}
#line 1487 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 250 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		current->me =strdup(yylval.varName);
   		(yyval.nPtr)= current;
    	}
#line 1497 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 255 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
		/*------------------------------------------------
			label mapping statement
		------------------------------------------------*/
		DEB(printf("Label: %s: %d\n", (yyvsp[-1].nPtr)->me,(yyvsp[0].nPtr)->num);)
		search.setName((yyvsp[-1].nPtr)->me);
		search.setOutMapping((yyvsp[0].nPtr)->num);
    		if (!labelList.query(search)){
			/* printf("Warning: label %s not mapped. Address=%d\n", $<nPtr>3->me,$4->num); */
			rtR2U2_print_label(&fp, 	
				(yyvsp[-1].nPtr)->me,
				(yyvsp[0].nPtr)->num,
				(yyvsp[0].nPtr)->thelogic,
				-1
				);
			search.setInfo((yyvsp[0].nPtr)->num);
			labelList.addItem(search);
			}
    		else {
			printf("Warning: label %s already mapped.\n", (yyvsp[-1].nPtr)->me);
			/* we already have the label mapped */
			rtR2U2_print_label(&fp, 	
				(yyvsp[-1].nPtr)->me,
				(yyvsp[0].nPtr)->num,
				(yyvsp[0].nPtr)->thelogic,
				labelList.addItem(search)
				);
			/* no idea why needs to be added again */
    			} 
		(yyval.nPtr)=(yyvsp[0].nPtr);
		}
#line 1533 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 291 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me =strdup(yylval.varName);
    		current->left_kid = NULL;
    		current->right_kid = NULL;

    		/*Check if we've declared this variable yet*/
    		search.setName(current->me);
    		used = varList.query(search);
		DEB(printf("PROP: used=%d\n",used));
    		current->num = used;
    		if (used == 0) { /*we haven't used this variable name yet*/
			/*Add the var to the list so we don't use it again*/
			current->num = varList.addItem(search);
			printf("WARNING: VAR %s not mapped -- use idx=%d\n",
			yylval.varName, current->num);
    			} 
     		else {
			//JSC ??? current->num = varList.find(search).getInfo();
			current->num = varList.addItem(search);
		    }
		
		DEB(printf("PROP: name >%s< id: %d\n", yylval.varName, current->num););

    		(yyval.nPtr) = current;
		}
#line 1566 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 324 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me =strdup(yylval.varName);

			// this marks that the name is an address
    		current->left_kid = current;
    		current->right_kid = current;

    		/*Check if we've declared this variable yet*/
    		search.setName(current->me);
    		used = labelList.query(search);
		DEB(printf("PROP: used=%d\n",used));
    		if (used == 0) { /*we haven't used this label name yet*/
			printf("ERROR: Label %s not defined\n", yylval.varName);
			yyerror("cannot use forward labels");
    			} 
     		else {
//JSC			current->num = varList.addItem(search);
			current->num = labelList.addItem(search);
//JSC2			current->num = varList.find(search).getOutMapping();
			}
    		(yyval.nPtr) = current;
		}
#line 1596 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 353 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
		NYI;   
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = (char *)malloc(6*sizeof(char));
    		if (current->me==NULL){ 
			fprintf(stderr, "Memory error25\n"); exit(1); }
    		strcpy(current->me, "TRUE"); /*copy in the operator*/

    		current->left_kid = NULL;
    		current->right_kid = NULL;

    		(yyval.nPtr) = current;
	}
#line 1616 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 372 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
	NYI;   
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = (char *)malloc(7*sizeof(char));
    		if (current->me==NULL){ 
			fprintf(stderr, "Memory error25\n"); exit(1); }
    		strcpy(current->me, "FALSE"); /*copy in the operator*/

    		current->left_kid = NULL;
    		current->right_kid = NULL;
    		(yyval.nPtr) = current;
	}
#line 1635 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 390 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = (char *)malloc(2*sizeof(char));
    		if (current->me==NULL){ 
			fprintf(stderr, "Memory error12\n"); exit(1); }

    		current->me[0] = '~'; /*copy in the operator*/
    		current->me[1] = '\0'; /*end the string*/
    		current->num = -1;

    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = (thelogic==ptLTL)?(OPC_NOT):(OPC_FT_NOT);
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
    		rtR2U2_print(&fp, current);

		if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op1 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op1==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op1->me = strdup("&");
    		  	current_op1->num = -1;
    		  	current_op1->left_kid = current;
    		  	current_op1->right_kid = current;
    		  	current_op1->left_kid->parent = current_op1;
    		  	current_op1->right_kid->parent = current_op1;
  
    		  	current_op1->num = ++mem_addr_ft;
    		  	current_op1->thelogic = thelogic;
    		  	current_op1->op = OPC_FT_AND;
    		  	current_op1->intvl.lb = -1;
    		  	current_op1->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op1);
			current = current_op1;
		}
    		(yyval.nPtr) = current;
	}
#line 1687 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 441 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("UP");
    		current->num = -1;

    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_START;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
    		rtR2U2_print(&fp, current);

    		(yyval.nPtr) = current;
	}
#line 1713 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 466 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("DOWN");
    		current->num = -1;

    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_END;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
    		rtR2U2_print(&fp, current);

    		(yyval.nPtr) = current;
	}
#line 1739 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 492 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = (char *)malloc(2*sizeof(char));
    		if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    		current->me[0] = 'X'; /*copy in the operator*/
    		current->me[1] = '\0'; /*end the string*/
    		/*fprintf(stderr, "Saving %s\n", current->me);*/
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_FT_FT;
    		current->intvl.lb = -1;
    		current->intvl.ub = 1;
    
    		rtR2U2_print(&fp, current);

    		(yyval.nPtr) = current;
	}
#line 1767 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 519 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("Y");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_PT_Y;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
    		rtR2U2_print(&fp, current);

    		(yyval.nPtr) = current;
	}
#line 1792 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 544 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("G");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->intvl.lb = (yyvsp[-1].intvl).lb;
    		current->intvl.ub = (yyvsp[-1].intvl).ub;
    		if (((yyvsp[-1].intvl).ub == -1) && ((yyvsp[-1].intvl).lb == -1)){
			yyerror("must have end time or interval");;
			}
		else {
		    if (thelogic == ptLTL){
    			current->op = ((yyvsp[-1].intvl).lb == -1)?OPC_PT_HT:OPC_PT_HJ;
			}
		    else {
printf("FT with %d\n", (yyvsp[-1].intvl).lb);
    			current->op = ((yyvsp[-1].intvl).lb == -1)?OPC_FT_GT:OPC_FT_GJ;
			}

	    		rtR2U2_print(&fp, current);
			}
    		(yyval.nPtr) = current;
	}
#line 1827 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 581 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("H");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->intvl.lb = (yyvsp[-1].intvl).lb;
    		current->intvl.ub = (yyvsp[-1].intvl).ub;

		if ((yyvsp[-1].intvl).lb == -1 ){
			if ((yyvsp[-1].intvl).ub == -1){
    				current->op = OPC_PT_H;
				}
			else {
    				current->op = OPC_PT_HT;
				}
			}
		else {
			current->op = OPC_PT_HJ;
			}
				
    		rtR2U2_print(&fp, current);

    		(yyval.nPtr) = current;
	}
#line 1863 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 618 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("F");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->intvl.lb = (yyvsp[-1].intvl).lb;
    		current->intvl.ub = (yyvsp[-1].intvl).ub;
    		if (((yyvsp[-1].intvl).ub == -1) && ((yyvsp[-1].intvl).lb == -1)){
			yyerror("must have end time or interval");;
			}
		else {
			current->op = ((yyvsp[-1].intvl).lb == -1)?OPC_FT_FT:OPC_FT_FJ;
    			rtR2U2_print(&fp, current);
		}
    		(yyval.nPtr) = current;
	}
#line 1891 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 648 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("O");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = (yyvsp[0].nPtr);
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_PT_O;
    		current->intvl.lb = (yyvsp[-1].intvl).lb;
    		current->intvl.ub = (yyvsp[-1].intvl).ub;
		if ((yyvsp[-1].intvl).lb == -1 ){
			if ((yyvsp[-1].intvl).ub == -1){
    				current->op = OPC_PT_O;
				}
			else {
    				current->op = OPC_PT_OT;
				}
			}
		else {
			current->op = OPC_PT_OJ;
			}
				
    		rtR2U2_print(&fp, current);

    		(yyval.nPtr) = current;
	}
#line 1927 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 683 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("&");
    		current->num = -1;
    		current->left_kid = (yyvsp[-2].nPtr);
    		current->right_kid = (yyvsp[0].nPtr);
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;
		
    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = (thelogic==ptLTL)?(OPC_AND):(OPC_FT_AND);
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
   		 
    		rtR2U2_print(&fp, current);
    		(yyval.nPtr) = current;
	}
#line 1951 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 706 "yaccrtR2U2.y" /* yacc.c:1646  */
    {

		if (thelogic != ftLTL){
   		  current = (struct node *)malloc(sizeof(struct node));
    		  if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		  current->me = strdup("|");
    		  current->num = -1;
    		  current->left_kid = (yyvsp[-2].nPtr);
    		  current->right_kid = (yyvsp[0].nPtr);
    		  current->left_kid->parent = current;
    		  current->right_kid->parent = current;
  
    		  current->num = ++mem_addr_pt;
    		  current->thelogic = thelogic;
    		  current->op = OPC_OR;
    		  current->intvl.lb = -1;
    		  current->intvl.ub = -1;
   		   
    		  rtR2U2_print(&fp, current);
    		  (yyval.nPtr) = current;
		}
		else {
			// use deMorgan's Law
			//
			// negate first formula
			//
		  current_op1 = (struct node *)malloc(sizeof(struct node));
    
		  if (current_op1==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		  current_op1->me = strdup("~");
    		  current_op1->num = -1;
    		  current_op1->left_kid = NULL;
    		  current_op1->right_kid = (yyvsp[-2].nPtr);
    		  current_op1->right_kid->parent = current_op1;
  
    		  current_op1->num = ++mem_addr_ft;
    		  current_op1->thelogic = thelogic;
    		  current_op1->op = OPC_FT_NOT;
    		  current_op1->intvl.lb = -1;
    		  current_op1->intvl.ub = -1;

		  rtR2U2_print(&fp, current_op1);

		  if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op2 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op2==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op2->me = strdup("&");
    		  	current_op2->num = -1;
    		  	current_op2->left_kid = current_op1;
    		  	current_op2->right_kid = current_op1;
    		  	current_op2->left_kid->parent = current_op2;
    		  	current_op2->right_kid->parent = current_op2;
  
    		  	current_op2->num = ++mem_addr_ft;
    		  	current_op2->thelogic = thelogic;
    		  	current_op2->op = OPC_FT_AND;
    		  	current_op2->intvl.lb = -1;
    		  	current_op2->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op2);
			current_op1 = current_op2;
		  }

			//
			// negate 2nd formula
			//
		  current_op2 = (struct node *)malloc(sizeof(struct node));
      
		  if (current_op2==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		  current_op2->me = strdup("~");
    		  current_op2->num = -1;
    		  current_op2->left_kid = NULL;
    		  current_op2->right_kid = (yyvsp[0].nPtr);
    		  current_op2->right_kid->parent = current_op2;

    		  current_op2->num = ++mem_addr_ft;
    		  current_op2->thelogic = thelogic;
    		  current_op2->op = OPC_FT_NOT;
    		  current_op2->intvl.lb = -1;
    		  current_op2->intvl.ub = -1;

		  rtR2U2_print(&fp, current_op2);

		  if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op3 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op3==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op3->me = strdup("&");
    		  	current_op3->num = -1;
    		  	current_op3->left_kid = current_op2;
    		  	current_op3->right_kid = current_op2;
    		  	current_op3->left_kid->parent = current_op3;
    		  	current_op3->right_kid->parent = current_op3;
  
    		  	current_op3->num = ++mem_addr_ft;
    		  	current_op3->thelogic = thelogic;
    		  	current_op3->op = OPC_FT_AND;
    		  	current_op3->intvl.lb = -1;
    		  	current_op3->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op3);
			current_op2 = current_op3;
		  }

			//
			// then the "&"
			//
   		  current = (struct node *)malloc(sizeof(struct node));
    		  if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		  current->me = strdup("|");
    		  current->num = -1;
    		  current->left_kid = current_op1;
    		  current->right_kid = current_op2;
    		  current->left_kid->parent = current;
    		  current->right_kid->parent = current;
  
    		  current->num = ++mem_addr_ft;
    		  current->thelogic = thelogic;
    		  current->op = OPC_FT_AND;
    		  current->intvl.lb = -1;
    		  current->intvl.ub = -1;
   		   
    		  rtR2U2_print(&fp, current);

			//
			// negate the result
			//
		  current2 = (struct node *)malloc(sizeof(struct node));
    
		  if (current2==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		  current2->me = strdup("~");
    		  current2->num = -1;
    		  current2->left_kid = NULL;
    		  current2->right_kid = current;
    		  current2->right_kid->parent = current;

    		  current2->num = ++mem_addr_ft;
    		  current2->thelogic = thelogic;
    		  current2->op = OPC_FT_NOT;
    		  current2->intvl.lb = -1;
    		  current2->intvl.ub = -1;

		  rtR2U2_print(&fp, current2);
		  if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op1 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op1==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op1->me = strdup("&");
    		  	current_op1->num = -1;
    		  	current_op1->left_kid = current2;
    		  	current_op1->right_kid = current2;
    		  	current_op1->left_kid->parent = current_op1;
    		  	current_op1->right_kid->parent = current_op1;
  
    		  	current_op1->num = ++mem_addr_ft;
    		  	current_op1->thelogic = thelogic;
    		  	current_op1->op = OPC_FT_AND;
    		  	current_op1->intvl.lb = -1;
    		  	current_op1->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op1);
			current2 = current_op1;
		  }

    		  (yyval.nPtr) = current2;
		}
	}
#line 2135 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 889 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
		if (thelogic != ftLTL){
    		  current = (struct node *)malloc(sizeof(struct node));
    		  if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		  current->me = strdup("->");
    		  current->num = -1;
    		  current->left_kid = (yyvsp[-2].nPtr);
    		  current->right_kid = (yyvsp[0].nPtr);
    		  current->left_kid->parent = current;
    		  current->right_kid->parent = current;
		
    		  current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		  current->thelogic = thelogic;
    		  current->op = (thelogic==ptLTL)?(OPC_IMPL):(OPC_FT_IMPL);
    		  current->intvl.lb = -1;
    		  current->intvl.ub = -1;
   		   
    		  rtR2U2_print(&fp, current);
    		  (yyval.nPtr) = current;
		}
		else {
			// use deMorgan's Law
			// A->B  ==>  ! (A & !B)
			//
			//
			// negate 2nd formula
			//
		  current_op2 = (struct node *)malloc(sizeof(struct node));
      
		  if (current_op2==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		  current_op2->me = strdup("~");
    		  current_op2->num = -1;
    		  current_op2->left_kid = NULL;
    		  current_op2->right_kid = (yyvsp[0].nPtr);
    		  current_op2->right_kid->parent = current_op2;

    		  current_op2->num = ++mem_addr_ft;
    		  current_op2->thelogic = thelogic;
    		  current_op2->op = OPC_FT_NOT;
    		  current_op2->intvl.lb = -1;
    		  current_op2->intvl.ub = -1;

		  rtR2U2_print(&fp, current_op2);

		  if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op3 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op3==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op3->me = strdup("&");
    		  	current_op3->num = -1;
    		  	current_op3->left_kid = current_op2;
    		  	current_op3->right_kid = current_op2;
    		  	current_op3->left_kid->parent = current_op3;
    		  	current_op3->right_kid->parent = current_op3;
  
    		  	current_op3->num = ++mem_addr_ft;
    		  	current_op3->thelogic = thelogic;
    		  	current_op3->op = OPC_FT_AND;
    		  	current_op3->intvl.lb = -1;
    		  	current_op3->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op3);
			current_op2 = current_op3;
		  }

			//
			// then the "&"
			//
   		  current = (struct node *)malloc(sizeof(struct node));
    		  if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		  current->me = strdup("|");
    		  current->num = -1;
    		  current->left_kid = (yyvsp[-2].nPtr);
    		  current->right_kid = current_op2;
    		  current->left_kid->parent = current;
    		  current->right_kid->parent = current;
  
    		  current->num = ++mem_addr_ft;
    		  current->thelogic = thelogic;
    		  current->op = OPC_FT_AND;
    		  current->intvl.lb = -1;
    		  current->intvl.ub = -1;
   		   
    		  rtR2U2_print(&fp, current);

			//
			// negate the result
			//
		  current2 = (struct node *)malloc(sizeof(struct node));
    
		  if (current2==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		  current2->me = strdup("~");
    		  current2->num = -1;
    		  current2->left_kid = NULL;
    		  current2->right_kid = current;
    		  current2->right_kid->parent = current;

    		  current2->num = ++mem_addr_ft;
    		  current2->thelogic = thelogic;
    		  current2->op = OPC_FT_NOT;
    		  current2->intvl.lb = -1;
    		  current2->intvl.ub = -1;

		  rtR2U2_print(&fp, current2);
		  if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op1 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op1==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op1->me = strdup("&");
    		  	current_op1->num = -1;
    		  	current_op1->left_kid = current2;
    		  	current_op1->right_kid = current2;
    		  	current_op1->left_kid->parent = current_op1;
    		  	current_op1->right_kid->parent = current_op1;
  
    		  	current_op1->num = ++mem_addr_ft;
    		  	current_op1->thelogic = thelogic;
    		  	current_op1->op = OPC_FT_AND;
    		  	current_op1->intvl.lb = -1;
    		  	current_op1->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op1);
			current2 = current_op1;
		  }

    		  (yyval.nPtr) = current2;
		}
	}
#line 2276 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 1029 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
		if (thelogic == ftLTL){
			printf("implement deMorgan");
			yyerror("operator not defined for future time");
			}
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("<->");
    		current->num = -1;
    		current->left_kid = (yyvsp[-2].nPtr);
    		current->right_kid = (yyvsp[0].nPtr);
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;
		
    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_EQUIVALENT;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
   		 
    		rtR2U2_print(&fp, current);
    		(yyval.nPtr) = current;
	}
#line 2305 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 1058 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    
		current = (struct node *)malloc(sizeof(struct node));
    
		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("U");
    		current->num = -1;
    		current->left_kid = (yyvsp[-3].nPtr);
    		current->right_kid = (yyvsp[0].nPtr);
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_FT_UJ;
    		current->intvl.lb = (yyvsp[-1].intvl).lb;
    		current->intvl.ub = (yyvsp[-1].intvl).ub;
    		if ((yyvsp[-1].intvl).lb == -1){
			yyerror("Until with intervals only");
			}
    		else {
    			rtR2U2_print(&fp, current);
			}
    		(yyval.nPtr) = current;
	}
#line 2336 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 1091 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    
		DEB(printf("handling RELEASE via transformation\n"));

			//
			// negate first formula
			//
		current_op1 = (struct node *)malloc(sizeof(struct node));
    
		if (current_op1==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		current_op1->me = strdup("~");
    		current_op1->num = -1;
    		current_op1->left_kid = NULL;
    		current_op1->right_kid = (yyvsp[-3].nPtr);
    		current_op1->right_kid->parent = current_op1;

    		current_op1->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current_op1->thelogic = thelogic;
    		current_op1->op = (thelogic==ptLTL)?(OPC_NOT):(OPC_FT_NOT);
    		current_op1->intvl.lb = -1;
    		current_op1->intvl.ub = -1;

		rtR2U2_print(&fp, current_op1);
		if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op2 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op2==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op2->me = strdup("&");
    		  	current_op2->num = -1;
    		  	current_op2->left_kid = current_op1;
    		  	current_op2->right_kid = current_op1;
    		  	current_op2->left_kid->parent = current_op2;
    		  	current_op2->right_kid->parent = current_op2;
  
    		  	current_op2->num = ++mem_addr_ft;
    		  	current_op2->thelogic = thelogic;
    		  	current_op2->op = OPC_FT_AND;
    		  	current_op2->intvl.lb = -1;
    		  	current_op2->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op2);
			current_op1 = current_op2;
		  }

			//
			// negate 2nd formula
			//
		current_op2 = (struct node *)malloc(sizeof(struct node));
    
		if (current_op2==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		current_op2->me = strdup("~");
    		current_op2->num = -1;
    		current_op2->left_kid = NULL;
    		current_op2->right_kid = (yyvsp[0].nPtr);
    		current_op2->right_kid->parent = current_op2;

    		current_op2->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current_op2->thelogic = thelogic;
    		current_op2->op = (thelogic==ptLTL)?(OPC_NOT):(OPC_FT_NOT);
    		current_op2->intvl.lb = -1;
    		current_op2->intvl.ub = -1;

		rtR2U2_print(&fp, current_op2);

		if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op3 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op3==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op3->me = strdup("&");
    		  	current_op3->num = -1;
    		  	current_op3->left_kid = current_op2;
    		  	current_op3->right_kid = current_op2;
    		  	current_op3->left_kid->parent = current_op3;
    		  	current_op3->right_kid->parent = current_op3;
  
    		  	current_op3->num = ++mem_addr_ft;
    		  	current_op3->thelogic = thelogic;
    		  	current_op3->op = OPC_FT_AND;
    		  	current_op3->intvl.lb = -1;
    		  	current_op3->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op3);
			current_op2 = current_op3;
		}
			//
			// then the "U"
			//
		current = (struct node *)malloc(sizeof(struct node));
    
		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		current->me = strdup("U");
    		current->num = -1;
    		current->left_kid = current_op1;
    		current->right_kid = current_op2;
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_FT_UJ;
    		current->intvl.lb = (yyvsp[-1].intvl).lb;
    		current->intvl.ub = (yyvsp[-1].intvl).ub;
    		if ((yyvsp[-1].intvl).lb == -1){
			yyerror("Until with intervals only");
			}
    		else {
    			rtR2U2_print(&fp, current);
			}

			//
			// negate the result
			//
		current2 = (struct node *)malloc(sizeof(struct node));
    
		if (current2==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		current2->me = strdup("~");
    		current2->num = -1;
    		current2->left_kid = NULL;
    		current2->right_kid = current;
    		current2->right_kid->parent = current;

    		current2->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current2->thelogic = thelogic;
    		current2->op = (thelogic==ptLTL)?(OPC_NOT):(OPC_FT_NOT);
    		current2->intvl.lb = -1;
    		current2->intvl.ub = -1;

		rtR2U2_print(&fp, current2);
		if (fix_ft_not && (thelogic == ftLTL)){
			/* FT "not" must be followed by an AND RES RES */
   		  	current_op1 = (struct node *)malloc(sizeof(struct node));
    		  	if (current_op1==NULL){ 
				fprintf(stderr, "Memory error11\n"); exit(1); }
    		  	current_op1->me = strdup("&");
    		  	current_op1->num = -1;
    		  	current_op1->left_kid = current2;
    		  	current_op1->right_kid = current2;
    		  	current_op1->left_kid->parent = current_op1;
    		  	current_op1->right_kid->parent = current_op1;
  
    		  	current_op1->num = ++mem_addr_ft;
    		  	current_op1->thelogic = thelogic;
    		  	current_op1->op = OPC_FT_AND;
    		  	current_op1->intvl.lb = -1;
    		  	current_op1->intvl.ub = -1;
   		   
    		  	rtR2U2_print(&fp, current_op1);
			current2 = current_op1;
		}


			//
			// return the top-level
			//
    		(yyval.nPtr) = current2;
	}
#line 2507 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 1263 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("S");
    		current->num = -1;
    		current->left_kid = (yyvsp[-3].nPtr);
    		current->right_kid = (yyvsp[0].nPtr);
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;
		
    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->intvl.lb = (yyvsp[-1].intvl).lb;
    		current->intvl.ub = (yyvsp[-1].intvl).ub;
		if ((yyvsp[-1].intvl).lb == -1){
			if ((yyvsp[-1].intvl).ub != -1){
				yyerror("Since not allowed with end time");
				}
			else {
    				current->op = OPC_PT_S;
    				rtR2U2_print(&fp, current);
				}
			}
		else {
			current->op = OPC_PT_SJ;
			rtR2U2_print(&fp, current);
			}

    		(yyval.nPtr) = current;
	}
#line 2542 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 1297 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
    		(yyval.nPtr) = (yyvsp[-1].nPtr);
	}
#line 2550 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 1312 "yaccrtR2U2.y" /* yacc.c:1646  */
    { 
		(yyval.intvl).lb=-1; (yyval.intvl).ub=-1;
	}
#line 2558 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 1322 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
		(yyval.intvl).lb=-1;
		(yyval.intvl).ub=(yyvsp[-1].numval);
	}
#line 2567 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 1331 "yaccrtR2U2.y" /* yacc.c:1646  */
    {
		if ((yyvsp[-3].numval) > (yyvsp[-1].numval)){
			yyerror("Upperbound cannot be lower than lower bound");
			}
		(yyval.intvl).lb=(yyvsp[-3].numval);
		(yyval.intvl).ub=(yyvsp[-1].numval);
	}
#line 2579 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
    break;


#line 2583 "yaccrtR2U2.tab.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 1342 "yaccrtR2U2.y" /* yacc.c:1906  */


		
		
extern int yyleng;
extern int yylineno;
extern char yytext[];

int yywhere() {  /* Fehlerplatzierung durch Bezug auf yytext */
register int colon=0;  /*nach Schreiner*/

printf(">>>>%c<<<\n",*yytext);
printf("yylineno = %d\n", yylineno);
printf("yyleng = %d\n", yyleng);

if (yylineno>0) {
  if (colon) fputs(", ",stdout);
   printf("line %d",yylineno-((*yytext=='\n')||(!*yytext)));
   colon=1;
  }
switch (*yytext) {
  case '\0':
  case '\n': break;
  default: if (colon) putchar(' ');
    printf("near \"%.*s\"",yyleng>20 ? 20 :
           yytext[yyleng-1]=='\n' ? yyleng-1 : yyleng,yytext);
    colon=1;
  }
if (colon) fputs(": ",stdout);

return 0;
}
	
