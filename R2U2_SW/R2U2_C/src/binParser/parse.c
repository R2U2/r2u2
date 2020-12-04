#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#include "TL_observers.h"
#include "TL_queue_ft.h"

#include "at_instruction.h"
#include "at_globals.h"
#include "filters/filter_rate.h"
#include "filters/filter_movavg.h"

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

void decode_at_instr(char* s, at_instruction_t* inst)
{
	// 1. index to place final atomic value
	inst->atom_addr = string2Int(&s,L_ATOMIC_ADDR);

	// 2. type of filter to apply to signal
	inst->filter = string2Int(&s,L_FILT);

	// 3. index of signal to read from signals_vector
	inst->sig_addr = string2Int(&s,L_SIG_ADDR);

	// 4. argument used for certain filters
	int arg = string2Int(&s,L_CONST);
	printf("\n%d\n", arg);

	// 5. type of comparison operator to apply
	inst->comp = string2Int(&s,L_COMP);

	// 6. value of constant to compare to filtered signal
	int constant = string2Int(&s,L_CONST);

	switch(inst->filter) {
		case OP_BOOL: {
			inst->comp_const.b = (bool) constant;
			break;
		}
		case OP_INT: {
			inst->comp_const.i = (int32_t) constant;
			break;
		}
		case OP_DOUBLE: {
			inst->comp_const.d = (double) constant;
			break;
		}
		case OP_RATE: {
			inst->comp_const.d = (double) constant;
			filter_rate_init((double *)&(inst->filt_data_struct.prev));
			break;
		}
		case OP_ABS_DIFF_ANGLE: {
			inst->comp_const.d = (double)constant;
			inst->filt_data_struct.diff_angle = (double) arg;
			break;
		}
		case OP_MOVAVG: {
			inst->comp_const.d = (double) constant;
			inst->filt_data_struct.movavg = *filter_movavg_init((uint16_t)arg);
			break;
		}
		default: {
			break;
		}
	}

}

//------------------------------------------------------------------------------
// Future Time Instruction Parser
//------------------------------------------------------------------------------
void parse_inst_ft(char* filename) {
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
//------------------------------------------------------------------------------
// Past Time Instruction Parser
//------------------------------------------------------------------------------
void parse_inst_pt(char* filename) {
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_inst(line, &instruction_mem_pt[PC]);
			// printf("%d\n",instruction_mem_ft[PC].op1.value);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}
//------------------------------------------------------------------------------
// Future-Time Interval Parser
//------------------------------------------------------------------------------
void parse_interval_ft(char* filename) {
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_interval(line, &interval_mem_ft[PC]);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}
//------------------------------------------------------------------------------
// Past-Time Interval Parser
//------------------------------------------------------------------------------
void parse_interval_pt(char* filename) {
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_interval(line, &interval_mem_pt[PC]);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}
//------------------------------------------------------------------------------
// SCQ Parser (only Future-Time; Past-Time doesn't use SCQs)
//------------------------------------------------------------------------------
void parse_scq_size(char* filename) {
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_scq_size(line, &addr_SCQ_map_ft[PC]);
			(SCQ+(addr_SCQ_map_ft[PC].start_addr))->t_q = -1; // initialize timestamp of the first elelment to -1
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}
//------------------------------------------------------------------------------
// AT Parser
//------------------------------------------------------------------------------
void parse_at(char *filename)
{
	int PC = 0;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [MAX_INSTR]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_at_instr(line, &at_instructions[PC]);
			PC++;
		}
		num_instr = PC; // set number of AT instructions
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}
