#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>

#include "parse.h"

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
	inst->filter = string2Int(&s,L_FILTER);

	// 3. index of signal to read from signals_vector
	inst->sig_addr = string2Int(&s,L_SIG_ADDR);

	// 4. argument used for certain filters
	int arg = string2Int(&s,L_NUM);

	// 5. type of comparison operator to apply
	inst->cond = string2Int(&s,L_COMP);

	// 6. is the comparison value a signal?
	inst->comp_is_sig = string2Int(&s,1);

	// 7. value of constant to compare to filtered signal
	int comp = string2Int(&s,L_NUM);

	// If comp is a signal, store index of signal in instruction
	if(inst->comp_is_sig) {
		inst->comp.s = (uint8_t) comp;
		switch(inst->filter) {
			case OP_RATE: {
				filter_rate_init(&inst->filt_data_struct.prev);
				break;
			}
			case OP_ABS_DIFF_ANGLE: {
				inst->filt_data_struct.diff_angle = (double) arg;
				break;
			}
			case OP_MOVAVG: {
				inst->filt_data_struct.movavg = filter_movavg_init((uint16_t)arg);
				break;
			}
			default: break;
		}
	} else { // Else store value as constant
		switch(inst->filter) {
			case OP_BOOL: inst->comp.b = (bool) comp;	break;
			case OP_INT: inst->comp.i = (int32_t) comp;	break;
			case OP_DOUBLE: inst->comp.d = (double) comp;	break;
			case OP_RATE: {
				inst->comp.d = (double) comp;
				filter_rate_init(&inst->filt_data_struct.prev);
				break;
			}
			case OP_ABS_DIFF_ANGLE: {
				inst->comp.d = (double) comp;
				inst->filt_data_struct.diff_angle = (double) arg;
				break;
			}
			case OP_MOVAVG: {
				inst->comp.d = (double) comp;
				inst->filt_data_struct.movavg = filter_movavg_init((uint16_t)arg);
				break;
			}
			default: 	break;
		}
	}
}

//------------------------------------------------------------------------------
// Future Time Instruction Parser
//------------------------------------------------------------------------------
void parse_inst_ft_file(char* filename) {
	int PC = 0;
	char line[MAX_LINE];

	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		while ( fgets (line, sizeof(line), file ) != NULL ) { /* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_inst(line, &instruction_mem_ft[PC]);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}

}
void parse_inst_ft_bin(char* bin) {
	int PC = 0;
	char *pch;
	char line[L_INSTRUCTION];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_INSTRUCTION);

	while ( pch != NULL ) {
		decode_inst(line, &instruction_mem_ft[PC]);
		PC++;
		memcpy(line, pch + 1, L_INSTRUCTION);
		pch = (char *) memchr(pch + 1, '\n', strlen(pch));
	}
}
//------------------------------------------------------------------------------
// Past Time Instruction Parser
//------------------------------------------------------------------------------
void parse_inst_pt_file(char* filename) {
	int PC = 0;
	char line[MAX_LINE];

	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_inst(line, &instruction_mem_pt[PC]);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
}
void parse_inst_pt_bin(char* bin) {
	int PC = 0;
	char *pch;
	char line[L_INSTRUCTION];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_INSTRUCTION);

	while ( pch != NULL ) {
		decode_inst(line, &instruction_mem_pt[PC]);
		PC++;
		memcpy(line, pch + 1, L_INSTRUCTION);
		pch = (char *) memchr(pch + 1, '\n', strlen(pch));
	}
}
//------------------------------------------------------------------------------
// Future-Time Interval Parser
//------------------------------------------------------------------------------
void parse_interval_ft_file(char* filename) {
	int PC = 0;
	char *pch;
	char line[MAX_LINE];

	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
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
void parse_interval_ft_bin(char* bin) {
	int PC = 0;
	char *pch;
	char line[L_INTERVAL*2];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_INTERVAL*2);

	while ( pch != NULL ) {
		decode_interval(line, &interval_mem_ft[PC]);
		PC++;
		memcpy(line, pch + 1, L_INTERVAL*2);
		pch = (char *) memchr(pch + 1, '\n', strlen(pch));
	}
}
//------------------------------------------------------------------------------
// Past-Time Interval Parser
//------------------------------------------------------------------------------
void parse_interval_pt_file(char* filename) {
	int PC = 0;
	char *pch;
	char line[MAX_LINE];

	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
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
void parse_interval_pt_bin(char* bin) {
	int PC = 0;
	char *pch;
	char line[L_INTERVAL*2];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_INTERVAL*2);

	while ( pch != NULL ) {
		decode_interval(line, &interval_mem_pt[PC]);
		PC++;
		memcpy(line, pch + 1, L_INTERVAL*2);
		pch = (char *) memchr(pch + 1, '\n', strlen(pch));
	}
}
//------------------------------------------------------------------------------
// SCQ Parser (only Future-Time; Past-Time doesn't use SCQs)
//------------------------------------------------------------------------------
void parse_scq_size_file(char* filename) {
	int PC = 0;
	char *pch;
	char line[MAX_LINE];

	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
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
void parse_scq_size_bin(char* bin) {
	int PC = 0;
	char *pch;
	char line[L_SCQ_ADDRESS];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_SCQ_ADDRESS);

	while ( pch != NULL ) {
			decode_scq_size(line, &addr_SCQ_map_ft[PC]);
			(SCQ+(addr_SCQ_map_ft[PC].start_addr))->t_q = -1; // initialize timestamp of the first elelment to -1
			PC++;
			memcpy(line, pch + 1, L_SCQ_ADDRESS);
			pch = (char *) memchr(pch + 1, '\n', strlen(pch));
		}
}

//------------------------------------------------------------------------------
// AT Parser
//------------------------------------------------------------------------------
void parse_at_file(char *filename)
{
	int PC = 0;
	char *pch;
	char line[MAX_LINE];

	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			decode_at_instr(line, &at_instructions[PC]);
			PC++;
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}

	num_instr = PC; // set number of AT instructions
}
void parse_at_bin(char *bin)
{
	int PC = 0;
	char *pch;
	char line[L_AT_INSTRUCTION];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_AT_INSTRUCTION);

	while ( pch != NULL && strlen(line) >=  L_AT_INSTRUCTION) {
		decode_at_instr(line, &at_instructions[PC]);
		PC++;
		memcpy(line, pch + 1, L_AT_INSTRUCTION);
		pch = (char *) memchr(pch + 1, '\n', strlen(pch));
	}

	num_instr = PC; // set number of AT instructions
}
