#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>

#include "KItem.h"
#include "KList.h"
#include "rtR2U2.h"

#ifdef DEBUG
#	define DEB(X)	X
#else
#	define DEB(X)
#endif

struct rtU2D2_files {
	FILE *map;
	FILE *maps;
	FILE *fasm_pt;
	FILE *f_pt;
	FILE *fd_pt;
	FILE *fasm_ft;
	FILE *f_ft;
	FILE *fd_ft;
	FILE *f_Cstruct_ft;
	FILE *f_Cstruct_pt;
	FILE *f_Cstruct_d_pt;
	FILE *f_Cstruct_d_ft;
	};

typedef enum {
	ptLTL=0,
	ftLTL
	} t_logic;

typedef struct {
	int lb;
	int ub;
	} t_intvl;

/* node in the parse tree*/
struct node {
    struct node *parent;
    char *me;
    int num; /*to use for numbering the nodes/subformulas*/
    struct node *left_kid;
    struct node *right_kid;
    t_logic  thelogic;
    t_intvl  intvl;
    t_op     	op;
};

#ifndef ROOT
#define ROOT

extern "C" {
/*Global Variables*/
extern struct node *root;     /*the root of the parse tree*/
extern KList varList;         /*list of used variables to avoid repeats*/
extern KList labelList;         /*list of used variables to avoid repeats*/

	// used logic and memory address counters
extern t_logic thelogic;
extern int mem_addr_ft;
extern int mem_addr_pt;

	// Cstructure generation
extern int generate_Cstruct;

extern int fix_ft_not;

extern FILE *yyin_save;

extern struct rtU2D2_files fp;
extern const char *rtR2U2_bop[];
extern const char *rtR2U2_aop[];

}

#endif


void i2b(char *s, int n, int w);
void get_operand(char *op, char *opb, struct node *n);

void rtR2U2_print(struct rtU2D2_files *fp, struct node *n);
void rtR2U2_print_label(struct rtU2D2_files *fp, 
	const char *labelname, 
	int address,
	int theLogic,
	int mapaddress);

void rtR2U2_print_timestamp(struct rtU2D2_files *fp, int stamp);
