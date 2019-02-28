
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include "main.h"

//#include "yaccrtR2U2.tab.h"

//JSC
//int yyparse(void);


/*Global Variables*/
struct node *root;       /*the root of the parse tree*/
KList varList;           /*list of used variables to avoid repeats*/
KList labelList;           /*list of used variables to avoid repeats*/

t_logic	thelogic = ptLTL;

	// 1 = generate C code data structures in addition
	// 0 = generate binary (ASCII) files only
int generate_Cstruct = 1;

int mem_addr_ft = -1;
int mem_addr_pt = -1;

	// must have a AND X,X  after X: NOT Y
int fix_ft_not  = 0;

	// represent:  F X as ~G ~X
int fix_ft_future = 1;

	// load atomic values in future-time with the OP_FT_LOD
int ft_atomic_load_operator = 1;

FILE *yyin_save = 0;

int syntax_errors = 0;

struct rtU2D2_files fp;

const char *rtR2U2_bop[] = {
	OP_START,
	OP_END,
	OP_END_SEQUENCE	,
	OP_NOP	,
	OP_NOT	,
	OP_AND	,
	OP_OR	,
	OP_IMPL	,
	OP_FT_NOT	,
	OP_FT_AND	,
	OP_FT_IMPL	,
	OP_EQUIVALENT,
	// past time operations
	OP_PT_Y	,	// 12
	OP_PT_O	,
	OP_PT_H	,
	OP_PT_S	,
	// metric past and future time operations
	// intervals
	OP_PT_HJ,	// 16
	OP_PT_OJ,
	OP_PT_SJ,
	OP_FT_GJ,
	OP_FT_FJ,
	OP_FT_UJ,
	// end time points
	OP_PT_HT,
	OP_PT_OT,
	OP_FT_GT,
	OP_FT_FT,
	OP_FT_LOD
	};

const char *rtR2U2_aop[] = {
	AOP_START,
	AOP_END,
	AOP_END_SEQUENCE	,
	AOP_NOP	,
	AOP_NOT	,
	AOP_AND	,
	AOP_OR	,
	AOP_IMPL	,
	AOP_FT_NOT	,
	AOP_FT_AND	,
	AOP_FT_IMPL	,
	AOP_EQUIVALENT,
	// past time operations
	AOP_PT_Y,	//12
	AOP_PT_O,
	AOP_PT_H,
	AOP_PT_S,
	// metric past and future time operations
	// intervals
	AOP_PT_HJ,	//16
	AOP_PT_OJ,
	AOP_PT_SJ,
	AOP_FT_GJ,
	AOP_FT_FJ,
	AOP_FT_UJ,
	// end time points
	AOP_PT_HT,
	AOP_PT_OT,
	AOP_FT_GT,
	AOP_FT_FT,
	AOP_FT_LOD
	};

void rtR2U2_print_final(struct rtU2D2_files fp);
void rtR2U2_print_initial(struct rtU2D2_files fp,char *outfile, int stamp);

//=================================================
int main(int argc, char **argv) {

    int stamp = 44; // why this value????



    short i, j;                 /*iterative variables*/
    short first;

    char *infile;
    char *outfile;

	char buf[255];

    extern node *yyparse();
    extern FILE *yyin;

    if (argc <= 1){
	printf("usage: r2u2prepare <modelfile>.txt\n");
	exit(2);
	}

   i=1;
    int verbose=255;

	/* TODO: check cmdline */

    if (!strcmp(argv[i],"-")){
		// FT - file

	yyin = stdin;
	outfile = argv[i+1];
    	if (verbose) {
		fprintf(stderr, "Got formula from stdin\n");
		fprintf(stderr, "writing files into %s\n", getcwd(NULL, 0));
    	}

	}
    else {
    	infile = argv[i];

    	if (verbose) {
		fprintf(stderr, "Got formula file %s\n", infile);
		fprintf(stderr, "writing files into %s\n", getcwd(NULL, 0));
    	}
    	yyin = fopen(infile, "r");
    	if (!yyin) {
		fprintf(stderr, "Could not open %s\n", argv[i]);
		exit(1);
    	}

	// outfile = strdup(infile);
	char *s = strrchr(infile,'/');
	if (!s){
		outfile = strdup(infile);
		}
	else {
		outfile = strdup(s+1);
		}

	if (strlen(infile) > 4){
		outfile[strlen(outfile)-4]='\0';
		}
	}


	// open output files
	sprintf(buf,"%s.map", outfile);
	if(!(fp.map = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.map\n", outfile);
		exit(2);
		}
	sprintf(buf,"%s.maps", outfile);
	if(!(fp.maps = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.maps\n", outfile);
		exit(2);
		}
	sprintf(buf,"%s.pts", outfile);
	if(!(fp.fasm_pt = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.pts\n", outfile);
		exit(2);
		}
	sprintf(buf,"%s.ptm", outfile);
	if(!(fp.f_pt = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.ptm\n", outfile);
		exit(2);
		}
	sprintf(buf,"%s.pti", outfile);
	if(!(fp.fd_pt = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.pti\n", outfile);
		exit(2);
		}
	sprintf(buf,"%s.fts", outfile);
	if(!(fp.fasm_ft = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.fts\n", outfile);
		exit(2);
		}
	sprintf(buf,"%s.ftm", outfile);
	if(!(fp.f_ft = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.ftm\n", outfile);
		exit(2);
		}
	sprintf(buf,"%s.fti", outfile);
	if(!(fp.fd_ft = fopen(buf, "w"))){
		fprintf(stderr, "Could not open %s.fti\n", outfile);
		exit(2);
		}

	if (generate_Cstruct){
		sprintf(buf,"%s_ft.c", outfile);
		if(!(fp.f_Cstruct_ft = fopen(buf, "w"))){
			fprintf(stderr, "Could not open %s_ft.c\n", outfile);
			exit(2);
			}

		sprintf(buf,"%s_pt.c", outfile);
		if(!(fp.f_Cstruct_pt = fopen(buf, "w"))){
			fprintf(stderr, "Could not open %s_pt.c\n", outfile);
			exit(2);
			}

		sprintf(buf,"%s_pti.c", outfile);
		if(!(fp.f_Cstruct_d_pt = fopen(buf, "w"))){
			fprintf(stderr, "Could not open %s_pti.c\n", outfile);
			exit(2);
			}

		sprintf(buf,"%s_fti.c", outfile);
		if(!(fp.f_Cstruct_d_ft = fopen(buf, "w"))){
			fprintf(stderr, "Could not open %s_fti.c\n", outfile);
			exit(2);
			}

		}

	rtR2U2_print_initial(fp, outfile, stamp);

	rtR2U2_print_timestamp(&fp, stamp);
    	yyparse();

    	if (verbose) {
		fprintf(stderr, "Done parsing\n");
    	}

	rtR2U2_print_final(fp);

	/* close files */
	fclose(fp.map);
	fclose(fp.maps);
	fclose(fp.fasm_pt);
	fclose(fp.f_pt);
	fclose(fp.fd_pt);
	fclose(fp.fasm_ft);
	fclose(fp.f_ft);
	fclose(fp.fd_ft);
	if (generate_Cstruct){
		fclose(fp.f_Cstruct_d_ft);
		fclose(fp.f_Cstruct_d_pt);
		fclose(fp.f_Cstruct_ft);
		fclose(fp.f_Cstruct_pt);
		}

    	if (verbose) {
		fprintf(stderr, "%d syntax errors found\n",syntax_errors);
    	}
    	if (syntax_errors) {
		exit(2);
		}
	else {
    		exit(0);
    		}
}
