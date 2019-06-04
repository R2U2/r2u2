#include <stdio.h>
#include <string.h>
#include "TL_observers.h"


static inline int string2Int(char** char_vec, int len) {
	int op = 0;
	for(int i=0;i<len;i++) {
		op = op<<1 | (*(*char_vec+i)-'0');
	}
	*char_vec += len; //skip the data that has been read
	return op;
}

void decode_inst(char* s, instruction_t* inst) {
	//1. operant code, 5 bits
	inst->opcode = string2Int(&s,L_OPC);

	//2. op1, 10 bits. First 2 bit is the input type
	inst->op1.opnd_type = string2Int(&s,2);
	inst->op1.value = string2Int(&s,L_OP-2);

	//3. op2, 10 bits. First 2 bit is the input type
	inst->op2.opnd_type = string2Int(&s,2);
	inst->op2.value = string2Int(&s,L_OP-2);

	//4. time stamp  address, 8 bits
	inst->adr_interval = string2Int(&s,L_INTVL);

	//5. scratch? 7 bits (seems for Bayesian network)
	inst->scratch = string2Int(&s,L_SCRATCH);
}

void decode_interval(char* s, interval_t* interval) {
	//1. lower bound, time stamp bits
	interval->lb = string2Int(&s,L_INTERVAL);

	//2. upper bound, time stamp bits
	interval->ub = string2Int(&s,L_INTERVAL);
}

void decode_scq_size(char* s, addr_SCQ_t* addr) {
	//1. start address
	addr->start_addr = string2Int(&s,L_SCQ_ADDRESS);

	//2. end address
	addr->end_addr = string2Int(&s,L_SCQ_ADDRESS);
} 

void parse_inst(char* filename) {
	// instruction_mem_t instruction_mem_ft={}; // use extern variable
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_inst(line, &instruction_mem_ft[PC]);			
			// printf("%d\n",instruction_mem_ft[PC].op1.value);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}

void parse_interval(char* filename) {
	interval_mem_t interval_mem_ft; // use extern variable
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_interval(line, &interval_mem_ft[PC]);
			// printf("%d\n",interval_mem_ft[address_count].lb);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}

void parse_scq_size(char* filename) {
	addr_SCQ_map_t addr_SCQ_map_ft ;
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_scq_size(line, &addr_SCQ_map_ft[PC]);
			printf("%d\n",addr_SCQ_map_ft[PC].start_addr);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}


void TL_init_files(char* ftm, char* fti, char* ftscq) {
	parse_inst(ftm);
	parse_interval(fti);
	parse_scq_size(ftscq);
}
