/* initialization from file -- NOT USED -- */
// Jun.3.2019 Pei: Don't use this file. The count of OP length is incorrect.
#include <stdio.h>
#include "TL_observers.h"

unsigned int s2b(const char *buf, int n);

int TL_init(const char *FN_ftm, const char *FN_fti,
	    const char *FN_ptm, const char *FN_pti,
	    const char *FN_map){

FILE *f;
char buf[255];

int  pc=0;
int  p_m_pt=0;
int  p_m_ft=0;


f=fopen(FN_ftm,"r");
printf("fjsenfwefnhsenhosefioefoiejf\n");
while (1){
	fgets(buf, L_INSTRUCTION+1, f);
	if (feof(f)){
		break;
		}
	fgetc(f);
	
	//  OPC:5 op1:10 op2:10 intvl:8 scratch:7
	instruction_mem_ft[pc].opcode 		= s2b(buf,L_OPC);
	instruction_mem_ft[pc].op1.opnd_type 	= s2b(buf+L_OPC,2);
	instruction_mem_ft[pc].op1.value 	= s2b(buf+L_OPC+2,L_OP);
	instruction_mem_ft[pc].op2.opnd_type 	= s2b(buf+L_OPC+L_OP,2);
	instruction_mem_ft[pc].op2.value 	= s2b(buf+L_OPC+L_OP+2,L_OP);
	instruction_mem_ft[pc].adr_interval 	= s2b(buf+L_OPC+2*L_OP,L_INTVL);
	instruction_mem_ft[pc].scratch	 	= s2b(buf+L_OPC+2*L_OP+L_INTVL,
							L_SCRATCH);

	pc++;
	}

printf("TL_init: %d instructions read from file %s.\n", pc,FN_ftm);
fclose(f);

//------------------------------------------------------
pc=0;
f=fopen(FN_ptm,"r");

printf("L_in = %d\n",L_INSTRUCTION);

while (1){
	fgets(buf, L_INSTRUCTION+1, f);
	if (feof(f)){
		break;
		}
	fgetc(f);
	
	//  OPC:5 op1:10 op2:10 intvl:8 scratch:7
	instruction_mem_pt[pc].opcode 		= s2b(buf,L_OPC);
	instruction_mem_pt[pc].op1.opnd_type 	= s2b(buf+L_OPC,2);
	instruction_mem_pt[pc].op1.value 	= s2b(buf+L_OPC+2,L_OP);
	instruction_mem_pt[pc].op2.opnd_type 	= s2b(buf+L_OPC+L_OP,2);
	instruction_mem_pt[pc].op2.value 	= s2b(buf+L_OPC+L_OP+2,L_OP);
	instruction_mem_pt[pc].adr_interval 	= s2b(buf+L_OPC+2*L_OP,L_INTVL);
	instruction_mem_pt[pc].scratch	 	= s2b(buf+L_OPC+2*L_OP+L_INTVL,
							L_SCRATCH);

	pc++;
	}

printf("TL_init: %d instructions read from file %s.\n", pc,FN_ptm);
fclose(f);

//------------------------------------------------------
p_m_pt=0;
p_m_ft=0;
f=fopen(FN_map,"r");

while (!feof(f)){
	fgets(buf, L_MAP+1, f);
	if (feof(f)){
		break;
		}
	fgetc(f);
	
	//  PT/FT: 1  VAL: 8
	if (s2b(buf, L_MAP_PTFT)){
		// FT
		map_mem_ft[p_m_ft++] 	= s2b(buf+L_MAP_PTFT, L_MAP_VALUE);
		}
	else {
		// PT
		map_mem_ft[p_m_pt++] 	= s2b(buf+L_MAP_PTFT, L_MAP_VALUE);
		}
	}

printf("TL_init: %d[ft] and %d[pt] map entries read from file %s.\n",
	p_m_ft, p_m_pt, FN_map);
fclose(f);

//------------------------------------------------------
pc=0;
f=fopen(FN_fti,"r");

while (!feof(f)){
	fgets(buf, L_INTERVAL+1, f);
	if (feof(f)){
		break;
		}
	fgetc(f);
	
	interval_mem_ft[pc].lb 	= s2b(buf,L_INTVL_TS);
	interval_mem_ft[pc].ub 	= s2b(buf+L_INTVL_TS, L_INTVL_TS);
	pc++;
	}

printf("TL_init: %d intervals read from file %s.\n", pc,FN_fti);
fclose(f);

//------------------------------------------------------
pc=0;
f=fopen(FN_pti,"r");

while (!feof(f)){
	fgets(buf, L_INTERVAL+1, f);
	if (feof(f)){
		break;
		}
	fgetc(f);
	
	interval_mem_pt[pc].lb 	= s2b(buf,L_INTVL_TS);
	interval_mem_pt[pc].ub 	= s2b(buf+L_INTVL_TS, L_INTVL_TS);
	pc++;
	}

printf("TL_init: %d intervals read from file %s.\n", pc,FN_pti);
fclose(f);


//------------------------------------------------------

return 0;
}

//--------------------------------------------------------------------
unsigned int s2b(const char *buf, int n){
	
int i;
unsigned val=0;

for (i=0; i < n; i++){
	val = (val <<1) + (buf[i] - '0');
	}

return val;

}



