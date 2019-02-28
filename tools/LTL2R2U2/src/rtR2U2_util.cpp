/*===============================================*/
/* utility stuff for the rtR2U2 assembler
*/

#include "main.h"

void i2b(char *s, int n, int w);
void get_operand(char *op, char *opb, struct node *n);

	// these addresses must be available from different
	// functions
static int ft_boxMemAddr = 0;
static int ft_untilMemAddr = 0;
static int ft_ts = 0; 
static int pt_boxMemAddr = 0;
static int pt_untilMemAddr = 0;
static int pt_ts = 0; 
static int has_pt_code = 0;
static int has_ft_code = 0;
static FILE *f;
static FILE *fd;
static FILE *fasm;
static FILE *f_Cstruct;
static FILE *f_Cstruct_d;

static char *(opcode_Cstruct[]) = {
	(char*)"OP_START",
	(char*)"OP_END",
	(char*)"OP_END_SEQUENCE",
	(char*)"OP_NOP",
	(char*)"OP_NOT",
	(char*)"OP_AND",
	(char*)"OP_OR",
	(char*)"OP_IMPL",
	(char*)"OP_FT_NOT",
	(char*)"OP_FT_AND",
	(char*)"OP_FT_IMPL",
	(char*)"OP_EQUIVALENT",
	// past time operations
	(char*)"OP_PT_Y",
	(char*)"OP_PT_O",
	(char*)"OP_PT_H",
	(char*)"OP_PT_S",
	// metric past and future time operations
	// intervals
	(char*)"OP_PT_HJ",
	(char*)"OP_PT_OJ",
	(char*)"OP_PT_SJ",
	(char*)"OP_FT_GJ",
	(char*)"OP_FT_FJ",
	(char*)"OP_FT_UJ",
	// end time points
	(char*)"OP_PT_HT",
	(char*)"OP_PT_OT",
	(char*)"OP_FT_GT",
	(char*)"OP_FT_FT",
	(char*)"OP_FT_LOD"
	};




/*********************************************************
	print current node into the rtU2D2 files
*********************************************************/
void rtR2U2_print(struct rtU2D2_files *fp, struct node *n) {

int *memAddr;
int *boxMemAddr;
int *untilMemAddr;
int *ts;

int i;
int ii;
char bbuf[41];
char tsbuf[255];
char ibuf[255];
char op1[255];
char op2[255];

	if (n->thelogic == ptLTL){
		// everything into PT files
		//
		f = fp->f_pt;
		fd = fp->fd_pt;
		fasm = fp->fasm_pt;
		ts = &pt_ts;
		boxMemAddr = &pt_boxMemAddr;
		untilMemAddr = &pt_untilMemAddr;
		if (generate_Cstruct){
			f_Cstruct = fp->f_Cstruct_pt;
			f_Cstruct_d = fp->f_Cstruct_d_pt;
			}
		has_pt_code = 1;

		}
	else {
		// everything into FT files
		//
		f = fp->f_ft;
		fd = fp->fd_ft;
		fasm = fp->fasm_ft;
		ts = &ft_ts;
		boxMemAddr = &ft_boxMemAddr;
		untilMemAddr = &ft_untilMemAddr;
		if (generate_Cstruct){
			f_Cstruct = fp->f_Cstruct_ft;
			f_Cstruct_d = fp->f_Cstruct_d_ft;
			}
		has_ft_code = 1;
		}

	if (n->op == OPC_FT_UJ || n->op == OPC_PT_SJ){
		memAddr = untilMemAddr;
		}
	else {
		memAddr = boxMemAddr;
		}

	for (i=0; i< 40; i++){
		*(bbuf+i) = '0';
		}
	bbuf[40] = '\0';
	tsbuf[0] = '\0';

	DEB(printf("DEB: %d %s %s\n", n->op, rtR2U2_aop[n->op],rtR2U2_bop[n->op]);)

		// operator
	for (i=0;i<5;i++){
		bbuf[i] = rtR2U2_bop[n->op][i];
		}

		// generate the C data structure
	if (generate_Cstruct){
		fprintf(f_Cstruct,"  { %s, ", opcode_Cstruct[n->op]);
		}
		

	if (n->left_kid == NULL && (n->right_kid)){
		// single operand operator -- right kid
		DEB(printf("single opnd\n");)
		get_operand(op1,bbuf+5,n->right_kid);
			//
			// other operand is empty
			//
		op2[0]='\0';
		if (generate_Cstruct){
			fprintf(f_Cstruct,"\t{ not_set, 0 }, ");
		}
		}
	else {
		// get operand(s)
	  if (n->left_kid){
		get_operand(op1,bbuf+5,n->left_kid);
		}
	  else {
		DEB(printf("no 1st op\n");)
		op1[0]='\0';
		if (generate_Cstruct){
			fprintf(f_Cstruct,"\t{ not_set, 0 }, ");
		}
		}
	  if (n->right_kid){
		get_operand(op2,bbuf+15,n->right_kid);
		}
	  else {
		DEB(printf("no 2nd op\n");)
		op2[0]='\0';
		if (generate_Cstruct){
			fprintf(f_Cstruct,"\t{ not_set, 0}, ");
		}
		}
	  }

		// get interval
	if (n->intvl.ub == -1){
		// not a temporal operator
		ibuf[0] = '\0';
		if (generate_Cstruct){
			fprintf(f_Cstruct,"\t0,");
			}
		}
	else {
	  i2b(bbuf+25,*ts, L_INTVL);
	  if (generate_Cstruct){
		fprintf(f_Cstruct,"\t%d,", *ts);
		}
	  DEB(printf("INTVL-addr: %d\n", *ts);)
	  if (n->intvl.lb == -1){
		// we have only T_e
		i2b(tsbuf,n->intvl.ub,2*L_INTVL_TS);
		tsbuf[2*L_INTVL_TS]='\0';
		sprintf(ibuf,"%d", n->intvl.ub);

	  	if (generate_Cstruct){
			fprintf(f_Cstruct_d,"{ %d, 0 },\n",n->intvl.ub);
			}
		}
	  else {
		i2b(tsbuf,n->intvl.lb,L_INTVL_TS);
		i2b(tsbuf+L_INTVL_TS,n->intvl.ub,L_INTVL_TS);
		tsbuf[2*L_INTVL_TS]='\0';
		sprintf(ibuf,"%d %d", n->intvl.lb, n->intvl.ub);
	  	if (generate_Cstruct){
			fprintf(f_Cstruct_d,"{ %d, %d },\n",
				n->intvl.lb,
				n->intvl.ub);
			}
		}
	  *ts = *ts + 1;

	  }
		// fill the scratchpad address
	  i2b(bbuf+33,*memAddr, L_PMEM);
	  DEB(printf("mem-addr: %d\n", *memAddr);)
	  if (generate_Cstruct){
		fprintf(f_Cstruct,"\t%d},\n", *memAddr);
		}
	  *memAddr = *memAddr+1;


	// now print the line

	fprintf(fasm,"%3.3d:\t\t%s\t%s\t%s\t%s\n",
		n->num,
		rtR2U2_aop[n->op],
		op1,
		op2,
		ibuf);

		// print binary code
	fprintf(f,"%s\n" ,bbuf);
#ifdef DEBUG2
	for (ii=0; ii< 41; ii++){
		printf("%x ",bbuf[ii]);
		}
	printf("\n");
#endif

		// print storage code
	if (*tsbuf){
		fprintf(fd,"%s\n" ,tsbuf);
		}
		
}

/*********************************************************
	print label info into the map file
*********************************************************/
void rtR2U2_print_label(struct rtU2D2_files *fp, 
	const char *labelname, 
	int address,
	int theLogic,
	int mapaddress){

char buf[17];

/* old format
	fprintf(fp->maps,"%s:\t%d[%s]\t%d\n", 
		labelname, 
		address,
		theLogic?"ft":"pt",
		mapaddress);
*/

	fprintf(fp->maps,"%d %3.3d %s\n", 
		theLogic,
		address,
		labelname);

	if (theLogic == ptLTL){
		buf[0] = '0';
		DEB(fprintf(fp->fasm_pt,"%s:\t %3.3d\n", labelname,address));
		}
	else {
		buf[0] = '1';
		DEB(fprintf(fp->fasm_ft,"%s:\t %3.3d\n", labelname,address));
		}

	i2b(buf+1, address, 8);

	if (mapaddress == -1){
		mapaddress = 0;
		}

	i2b(buf+9, mapaddress, 6);
	buf[15] = '0';

	buf[16]='\0';

	fprintf(fp->map, "%16.16s\n", buf);

}
		
		
/*********************************************************
	get_operand and return as string or 01 string
	in given buffers
*********************************************************/
void get_operand(char *op, char *opb, struct node *n){

DEB(printf("get_operand: num=%d\n",n->num);)

    if (!(n->left_kid) && !(n->right_kid)){
	if (n->me == NULL){
		// this a false or true
		sprintf(op,"i%3.3d",n->num);
		opb[0] = '0';
		opb[1] = '1';
		i2b(opb+2, n->num, L_OP-2);
		if (generate_Cstruct){
			fprintf(f_Cstruct,"\t{ direct, %d },", n->num);
			}
		}
	else {
		// regular variable (atomic)
		sprintf(op,"a%3.3d",n->num);
		opb[0] = '0';
		opb[1] = '0';
		i2b(opb+2, n->num, L_OP-2);
		if (generate_Cstruct){
			fprintf(f_Cstruct,"\t{ atomic, %d },", n->num);
			}
		}
	}
    else {
	//
	// subformula
	sprintf(op,"s%3.3d",n->num);
	opb[0] = '1';
	opb[1] = '0';
	i2b(opb+2, n->num, L_OP-2);
		if (generate_Cstruct){
			fprintf(f_Cstruct,"\t{ subformula, %d },", n->num);
			}
	}
}
		
/*********************************************************
	print initial timestamp into the pti file
*********************************************************/
void rtR2U2_print_timestamp(struct rtU2D2_files *fp, int stamp) {


char buf[40];
i2b(buf,stamp, 2*L_TIMESTAMP);
buf[2*L_TIMESTAMP] = '\0';
fprintf(fp->fd_pt,"%s\n",buf);

	// to make space for the "44"
pt_ts = 1;
}

/*********************************************************
	print final info into Cstruct files
*********************************************************/
void rtR2U2_print_final(struct rtU2D2_files fp){

if (generate_Cstruct){
	  if (!has_pt_code){
		/* put in END_OF SEQUENCE  code */
	  	fprintf(fp.f_Cstruct_pt,
		  "  { OP_END,\t\t{ not_set, 0 },\t{ not_set, 0},\t0,\t0}\n");
		}
	  fprintf(fp.f_Cstruct_pt,"};\n");

	  if (!has_ft_code){
		/* put in END_OF SEQUENCE  code */
	  	fprintf(fp.f_Cstruct_ft,
		  "  { OP_END,\t\t{ not_set, 0 },\t{ not_set, 0},\t0,\t0}\n");
		}
	  fprintf(fp.f_Cstruct_ft,"};\n");
	  fprintf(fp.f_Cstruct_d_pt,"};\n");
	  fprintf(fp.f_Cstruct_d_pt,
		"int l_interval_mem_pt = %d;\n", pt_ts);
	  fprintf(fp.f_Cstruct_d_ft,"};\n");
	}
}

/*********************************************************
	print final info into Cstruct files
*********************************************************/
void rtR2U2_print_initial(struct rtU2D2_files fp, char *outfile, int stamp){
if (generate_Cstruct){
	  fprintf(fp.f_Cstruct_pt,"/* auto-generated -- do not modify */\n");
	  fprintf(fp.f_Cstruct_pt,"/* Source: %s.txt\t\t*/\n",outfile);
	  fprintf(fp.f_Cstruct_pt,"\n\n");
	  fprintf(fp.f_Cstruct_pt,"#include \"TL_observers.h\"\n\n");
	  fprintf(fp.f_Cstruct_pt,"instruction_mem_t\tinstruction_mem_pt = {\n\n");

	  fprintf(fp.f_Cstruct_ft,"/* auto-generated -- do not modify */\n");
	  fprintf(fp.f_Cstruct_ft,"/* Source: %s.txt\t\t*/\n",outfile);
	  fprintf(fp.f_Cstruct_ft,"\n\n");
	  fprintf(fp.f_Cstruct_ft,"#include \"TL_observers.h\"\n\n");
	  fprintf(fp.f_Cstruct_ft,"instruction_mem_t\tinstruction_mem_ft = {\n\n");

	  fprintf(fp.f_Cstruct_d_pt,"/* auto-generated -- do not modify */\n");
	  fprintf(fp.f_Cstruct_d_pt,"/* Source: %s.txt\t\t*/\n",outfile);
	  fprintf(fp.f_Cstruct_d_pt,"\n\n");
	  fprintf(fp.f_Cstruct_d_pt,"#include \"TL_observers.h\"\n\n");
	  fprintf(fp.f_Cstruct_d_pt,"interval_t\tinterval_mem_pt[] = {\n\n");
		// this is some legacy wrt the FPGA implementation
	  fprintf(fp.f_Cstruct_d_pt,"{ %d, %d },\n",stamp, stamp);

	  fprintf(fp.f_Cstruct_d_ft,"/* auto-generated -- do not modify */\n");
	  fprintf(fp.f_Cstruct_d_ft,"/* Source: %s.txt\t\t*/\n",outfile);
	  fprintf(fp.f_Cstruct_d_ft,"\n\n");
	  fprintf(fp.f_Cstruct_d_ft,"#include \"TL_observers.h\"\n\n");
	  fprintf(fp.f_Cstruct_d_ft,"interval_t\tinterval_mem_ft[] = {\n\n");

	  }
}

/*********************************************************
	convert integer (unsigned) to n-bit string
	NOTE: string not null terminated
*********************************************************/
void i2b(char *s, int n, int w){

int i;

for(i=0; i< w; i++){
	s[w-i-1] = (n & 1) + '0';
	n = n >> 1;
	}
//s[i]='\0';

}
