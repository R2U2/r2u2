%{

/*
based on yaccLTL.cc
K.Y.Rozier
June, 2011
*/

/* This is a parser for LTL formulas in in-fix order */

#include "main.h"

#define NYI printf("JSC: NYI\n");


int yylex (void);

extern FILE *yyin;
extern int syntax_errors;

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
    syntax_errors++;
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
extern int fix_ft_future;
extern int ft_atomic_load_operator;

/*for parsing the formula string*/
#undef YY_INPUT
#define YY_INPUT(b, r, ms) (r = my_yyinput(b, me))

%}

%union {
    struct node *nPtr;		/* node pointer */
    char *varName;              /* name of a variable */
    int numval;
    int floatval;
    struct {int lb; int ub;} intvl;
};

%token AND OR NOT IMPLIES NEXT PREV SINCE UNTIL GLOBALLY LPAREN RPAREN
%token RELEASE 
%token EQUIV UP DOWN CONST MAP LMAP LOGIC INCLUDE
%token ATOMIC
%token PT FT 
%token ONCE HISTORICALLY
%token <varName> PROP 
%token <varName> STRING
%token FFALSE TTRUE
%token <numval> NUMBER 
%token <floatval> FLOAT

/* Establish precedence rules and left-associativity*/
/* (different from SMV -- I think ~ should bind tighter than U) */
%left '.'          /*  end of sub-formula (will be anded)    */
%left UNTIL        /*   until   */
%left RELEASE      /*   release   */
%left SINCE        /*   since   */
%left EQUIV        /*     <->    */
%left IMPLIES      /*     ->    */
%left OR           /*     or    */
%left AND          /*    and    */
%nonassoc ':'
%nonassoc GLOBALLY /*    globally   */
%nonassoc HISTORICALLY
%nonassoc FUTURE   /* in the future */
%nonassoc ONCE   /* in the future */
%nonassoc NEXT     /*   next time   */
%nonassoc PREV     /*   previously   */

%nonassoc LABELREF /* reference to label */
%nonassoc NOT      /*      not      */
%nonassoc UP       /*      up      */
%nonassoc DOWN     /*      down      */
%nonassoc PROP
%nonassoc NUMBER
%nonassoc TTRUE
%nonassoc FFALSE

%type <nPtr> input formula formula_stmt
%type <intvl> interval 

%%

/*********************************************************
	top of parse tree: input
*********************************************************/
input: 

INCLUDE STRING '.'
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

| formula_stmt '.'
	{
	DEB(printf("SINGLE FSTMT: %x %d\n",$1,($1)?$1->num:-1));
	}
| formula_stmt '.' input
	{
	DEB(printf("FSTMT: %x %d     ",$1,($1)?$1->num:-1));
	DEB(printf("INPUT: %x %d\n",$3,($3)?$3->num:-1));
	}
	
/*********************************************************
	formula_stmt
*********************************************************/
formula_stmt:
	/*------------------------------------------------
		formula
	------------------------------------------------*/
	formula { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); 
			}
	    	current->me = strdup("end");
    		current->left_kid = NULL;
    		current->right_kid = $1;
    		current->right_kid->parent = current;
    		current->thelogic = thelogic;
        	current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->op = OPC_END_SEQUENCE;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
	    	rtR2U2_print(&fp, current);

		// Label for default formula
		DEB(printf("Label: %s: %3.3d\n", "DEFAULT" ,$1->num+1););
		rtR2U2_print_label(&fp, 
			$1->thelogic?"ftDEFAULT":"ptDEFAULT", 
			$1->num+1,
			$1->thelogic,
			-1);

    		$$ = $1;
		}

	/*------------------------------------------------
		select logic
	------------------------------------------------*/
| LOGIC LPAREN logicID RPAREN 
		{
		printf("logic set to: %d\n", thelogic);
		$$ = NULL;
		}

	/*------------------------------------------------
		mapping statement
	------------------------------------------------*/
| MAP  PROP '=' NUMBER 
		{
    		search.setName($2);
    		if (varList.query(search)){
			printf("Error: %s redefined\n", $2);
			}
    		else {
			printf("MAP:variable %s added with index %d\n",$2,$4);
			search.setInfo($4);
			varList.addItem(search);
    			} 
		$$ = NULL;
    		}

	/*------------------------------------------------
		label mapping statement
	------------------------------------------------*/
| LMAP  PROP '=' NUMBER 
		{
    		search.setName($2);
    		if (labelList.query(search)){
			printf("Error: %s redefined\n", $2);
			}
    		else {
			printf("MAP:label %s added with index %d\n",$2,$4);
			search.setInfo($4);
			labelList.addItem(search);
    			} 
		$$ = NULL;
    		}
;

/*********************************************************
	type of logic
*********************************************************/
logicID: 
	PT 	{thelogic = ptLTL;}
|	FT 	{thelogic = ftLTL;}
;


/*********************************************************
	formula
*********************************************************/
formula: 
	/*------------------------------------------------
		labeled propositional formula
	------------------------------------------------*/
PROP ':' {
    		current = (struct node *)malloc(sizeof(struct node));
    		current->me =strdup(yylval.varName);
   		$<nPtr>$= current;
    	}
	formula {
		/*------------------------------------------------
			label mapping statement
		------------------------------------------------*/
		DEB(printf("Label: %s: %d\n", $<nPtr>3->me,$4->num);)
		search.setName($<nPtr>3->me);
		search.setOutMapping($4->num);
    		if (!labelList.query(search)){
			/* printf("Warning: label %s not mapped. Address=%d\n", $<nPtr>3->me,$4->num); */
			rtR2U2_print_label(&fp, 	
				$<nPtr>3->me,
				$4->num,
				$4->thelogic,
				-1
				);
			search.setInfo($4->num);
			labelList.addItem(search);
			}
    		else {
			printf("Warning: label %s already mapped.\n", $<nPtr>3->me);
			/* we already have the label mapped */
			rtR2U2_print_label(&fp, 	
				$<nPtr>3->me,
				$4->num,
				$4->thelogic,
				labelList.addItem(search)
				);
			/* no idea why needs to be added again */
    			} 
		$$=$4;
		}

	/*------------------------------------------------
		propositional variable
	------------------------------------------------*/
| PROP 
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
			printf("ERROR: VAR %s not mapped -- use idx=%d\n",
			yylval.varName, current->num);
			syntax_errors++;
    			} 
     		else {
			//JSC ??? current->num = varList.find(search).getInfo();
			current->num = varList.addItem(search);
		    }
		
		DEB(printf("PROP: name >%s< id: %d\n", yylval.varName, current->num););

		if (ft_atomic_load_operator && (thelogic==ftLTL)){
			//
			// we generate a OP_FT_LOD instruction
			//
		  current_op1 = (struct node *)malloc(sizeof(struct node));
    
		  if (current_op1==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		  current_op1->me = strdup("load_ft");
    		  current_op1->num = -1;
    		  current_op1->left_kid = NULL;
    		  current_op1->right_kid = current;
    		  current_op1->right_kid->parent = current_op1;
  
    		  current_op1->num = ++mem_addr_ft;
    		  current_op1->thelogic = thelogic;
    		  current_op1->op = OPC_FT_LOD;
    		  current_op1->intvl.lb = -1;
    		  current_op1->intvl.ub = -1;

		  rtR2U2_print(&fp, current_op1);
    		  $$ = current_op1;
		  }
		else {
    		  $$ = current;
		  }
		}

	/*------------------------------------------------
		label reference    @ label
	------------------------------------------------*/
| LABELREF PROP 
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
    		$$ = current;
		}

	/*------------------------------------------------
		constant TRUE
	------------------------------------------------*/
| TTRUE { 
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

    		$$ = current;
	}

	/*------------------------------------------------
		constant FALSE
	------------------------------------------------*/
| FFALSE { 
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
    		$$ = current;
	}

	/*------------------------------------------------
		~ formula
	------------------------------------------------*/
| NOT formula {
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
    		current->right_kid = $2;
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
    		$$ = current;
	}

	/*------------------------------------------------
		UP formula
	------------------------------------------------*/
| UP formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("UP");
    		current->num = -1;

    		current->left_kid = NULL;
    		current->right_kid = $2;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_START;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
    		rtR2U2_print(&fp, current);

    		$$ = current;
	}

	/*------------------------------------------------
		DOWN formula
	------------------------------------------------*/
| DOWN formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("DOWN");
    		current->num = -1;

    		current->left_kid = NULL;
    		current->right_kid = $2;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_END;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
    		rtR2U2_print(&fp, current);

    		$$ = current;
	}

	/*------------------------------------------------
		X formula (next)
    	NOTE:   X f   == F[1] 
	------------------------------------------------*/
| NEXT formula { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = (char *)malloc(2*sizeof(char));
    		if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    		current->me[0] = 'X'; /*copy in the operator*/
    		current->me[1] = '\0'; /*end the string*/
    		/*fprintf(stderr, "Saving %s\n", current->me);*/
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = $2;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_FT_FT;
    		current->intvl.lb = -1;
    		current->intvl.ub = 1;
    
    		rtR2U2_print(&fp, current);

    		$$ = current;
	}

	/*------------------------------------------------
		Y formula  (previous)
	------------------------------------------------*/
| PREV formula { 
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("Y");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = $2;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_PT_Y;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
    
    		rtR2U2_print(&fp, current);

    		$$ = current;
	}

	/*------------------------------------------------
		G [intvl] formula 
		G [t] formula 
	------------------------------------------------*/
| GLOBALLY interval formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("G");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = $3;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->intvl.lb = $2.lb;
    		current->intvl.ub = $2.ub;
    		if (($2.ub == -1) && ($2.lb == -1)){
			yyerror("must have end time or interval");;
			}
		else {
		    if (thelogic == ptLTL){
    			current->op = ($2.lb == -1)?OPC_PT_HT:OPC_PT_HJ;
			}
		    else {
printf("FT with %d\n", $2.lb);
    			current->op = ($2.lb == -1)?OPC_FT_GT:OPC_FT_GJ;
			}

	    		rtR2U2_print(&fp, current);
			}
    		$$ = current;
	} 

	/*------------------------------------------------
		historically
		H 			OP_PT_H
		H[t] 			OP_PT_HT
		H[t,t]			OP_PT_HJ
	------------------------------------------------*/
| HISTORICALLY interval formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("H");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = $3;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->intvl.lb = $2.lb;
    		current->intvl.ub = $2.ub;

		if ($2.lb == -1 ){
			if ($2.ub == -1){
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

    		$$ = current;
	} 

	/*------------------------------------------------
		future
		F[t]
		F[t,t]
	------------------------------------------------*/
| FUTURE interval formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("F");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = $3;
    		current->right_kid->parent = current;

    		if (thelogic==ptLTL){
			yyerror("F operator: future time only");
			}

		if (!fix_ft_future){
			//
			// we have the F operator
			//
    			current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    			current->thelogic = thelogic;
    			current->intvl.lb = $2.lb;
    			current->intvl.ub = $2.ub;
    			if (($2.ub == -1) && ($2.lb == -1)){
				yyerror("must have end time or interval");;
				}
			else {
				current->op = ($2.lb == -1)?OPC_FT_FT:OPC_FT_FJ;
    				rtR2U2_print(&fp, current);
				}
    		        $$ = current2;
			}
		else {
			//
			// F X  is ! G ! X
			//

			//
			// negate formula
			//
		  current_op1 = (struct node *)malloc(sizeof(struct node));
    
		  if (current_op1==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }

    		  current_op1->me = strdup("~");
    		  current_op1->num = -1;
    		  current_op1->left_kid = NULL;
    		  current_op1->right_kid = $3;
    		  current_op1->right_kid->parent = current_op1;
  
    		  current_op1->num = ++mem_addr_ft;
    		  current_op1->thelogic = thelogic;
    		  current_op1->op = OPC_FT_NOT;
    		  current_op1->intvl.lb = -1;
    		  current_op1->intvl.ub = -1;

		  rtR2U2_print(&fp, current_op1);

			//
			// then the "G" operator
			//
   		  current = (struct node *)malloc(sizeof(struct node));
    		  if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		  current->me = strdup("G");
    		  current->num = -1;
    		  current->left_kid = NULL;
    		  current->right_kid = current_op1;
    		  current->right_kid->parent = current;
    		  current->num = ++mem_addr_ft;
    		  current->thelogic = thelogic;
    		  current->op = OPC_FT_AND;
    		  current->intvl.lb = $2.lb;
    		  current->intvl.ub = $2.ub;
    		  if (($2.ub == -1) && ($2.lb == -1)){
			yyerror("must have end time or interval");;
			}
    		  current->op = ($2.lb == -1)?OPC_FT_GT:OPC_FT_GJ;
   		   
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
		  if (fix_ft_not){
				yyerror("internal: fix_ft_not not compatible with fit_ft_future");
				}
    		  $$ = current2;
		  	}
	} 

	/*------------------------------------------------
		ONCE
		O formula 		OP_PT_O
		O[t] formula		OP_PT_OT
		O[t,t] formula		OP_PT_OJ
	------------------------------------------------*/
| ONCE interval formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("O");
    		current->num = -1;
    		current->left_kid = NULL;
    		current->right_kid = $3;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_PT_O;
    		current->intvl.lb = $2.lb;
    		current->intvl.ub = $2.ub;
		if ($2.lb == -1 ){
			if ($2.ub == -1){
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

    		$$ = current;
	} 

	/*------------------------------------------------
		AND
	------------------------------------------------*/
| formula AND formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("&");
    		current->num = -1;
    		current->left_kid = $1;
    		current->right_kid = $3;
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;
		
    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = (thelogic==ptLTL)?(OPC_AND):(OPC_FT_AND);
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
   		 
    		rtR2U2_print(&fp, current);
    		$$ = current;
	}

	/*------------------------------------------------
		OR
	------------------------------------------------*/
| formula OR formula {

		if (thelogic != ftLTL){
   		  current = (struct node *)malloc(sizeof(struct node));
    		  if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		  current->me = strdup("|");
    		  current->num = -1;
    		  current->left_kid = $1;
    		  current->right_kid = $3;
    		  current->left_kid->parent = current;
    		  current->right_kid->parent = current;
  
    		  current->num = ++mem_addr_pt;
    		  current->thelogic = thelogic;
    		  current->op = OPC_OR;
    		  current->intvl.lb = -1;
    		  current->intvl.ub = -1;
   		   
    		  rtR2U2_print(&fp, current);
    		  $$ = current;
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
    		  current_op1->right_kid = $1;
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
    		  current_op2->right_kid = $3;
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

    		  $$ = current2;
		}
	}

	/*------------------------------------------------
		->
	------------------------------------------------*/
| formula IMPLIES formula {
		if (thelogic != ftLTL){
    		  current = (struct node *)malloc(sizeof(struct node));
    		  if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		  current->me = strdup("->");
    		  current->num = -1;
    		  current->left_kid = $1;
    		  current->right_kid = $3;
    		  current->left_kid->parent = current;
    		  current->right_kid->parent = current;
		
    		  current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		  current->thelogic = thelogic;
    		  current->op = (thelogic==ptLTL)?(OPC_IMPL):(OPC_FT_IMPL);
    		  current->intvl.lb = -1;
    		  current->intvl.ub = -1;
   		   
    		  rtR2U2_print(&fp, current);
    		  $$ = current;
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
    		  current_op2->right_kid = $3;
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
    		  current->left_kid = $1;
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

    		  $$ = current2;
		}
	}

	/*------------------------------------------------
		<->
	------------------------------------------------*/
| formula EQUIV formula {
		if (thelogic == ftLTL){
			printf("implement deMorgan");
			yyerror("operator not defined for future time");
			}
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("<->");
    		current->num = -1;
    		current->left_kid = $1;
    		current->right_kid = $3;
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;
		
    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_EQUIVALENT;
    		current->intvl.lb = -1;
    		current->intvl.ub = -1;
   		 
    		rtR2U2_print(&fp, current);
    		$$ = current;
	}

	/*------------------------------------------------
		until
		formula U[t1,t2] formula
	------------------------------------------------*/
| formula UNTIL interval formula {
    
		current = (struct node *)malloc(sizeof(struct node));
    
		if (current==NULL){ 
			fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("U");
    		current->num = -1;
    		current->left_kid = $1;
    		current->right_kid = $4;
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;

    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->op = OPC_FT_UJ;
    		current->intvl.lb = $3.lb;
    		current->intvl.ub = $3.ub;
    		if ($3.lb == -1){
			yyerror("Until with intervals only");
			}
    		else {
    			rtR2U2_print(&fp, current);
			}
    		$$ = current;
	}

	/*------------------------------------------------
		release
		formula R[t1,t2] formula
	implemented as transform:
		A R B ==  ! (!A U !B)
	------------------------------------------------*/
| formula RELEASE interval formula {
    
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
    		current_op1->right_kid = $1;
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
    		current_op2->right_kid = $4;
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
    		current->intvl.lb = $3.lb;
    		current->intvl.ub = $3.ub;
    		if ($3.lb == -1){
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
    		$$ = current2;
	}

	/*------------------------------------------------
		since
		formula S[t1,t2] formula
		formula S formula
	------------------------------------------------*/
| formula SINCE interval formula {
    		current = (struct node *)malloc(sizeof(struct node));
    		if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    		current->me = strdup("S");
    		current->num = -1;
    		current->left_kid = $1;
    		current->right_kid = $4;
    		current->left_kid->parent = current;
    		current->right_kid->parent = current;
		
    		current->num = (thelogic==ptLTL)?(++mem_addr_pt):(++mem_addr_ft);
    		current->thelogic = thelogic;
    		current->intvl.lb = $3.lb;
    		current->intvl.ub = $3.ub;
		if ($3.lb == -1){
			if ($3.ub != -1){
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

    		$$ = current;
	}

	/*------------------------------------------------
		parenthesis
	------------------------------------------------*/
| LPAREN formula RPAREN { 
    		$$ = $2;
	}
;



/*********************************************************
	interval
*********************************************************/
	/*------------------------------------------------
		empty interval
		lb=ub= -1
	------------------------------------------------*/
interval: 
    		{ 
		$$.lb=-1; $$.ub=-1;
	}

	/*------------------------------------------------
		time point 
		[NUMBER]
		lb= -1; ub = NUMBER
	------------------------------------------------*/
| '[' NUMBER ']'
		{
		$$.lb=-1;
		$$.ub=$2;
	}

	/*------------------------------------------------
		[NU, NU] interval
	------------------------------------------------*/
| '[' NUMBER ',' NUMBER ']'
		{
		if ($2 > $4){
			yyerror("Upperbound cannot be lower than lower bound");
			}
		$$.lb=$2;
		$$.ub=$4;
	}
;


/**********END OF GRAMMAR********************************/
%%

		
		
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
	
