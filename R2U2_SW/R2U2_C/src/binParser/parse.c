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
	inst->filter = string2Int(&s,L_FILT);

	// 3. index of signal to read from signals_vector
	inst->sig_addr = string2Int(&s,L_SIG_ADDR);

	// 4. argument used for certain filters
	int arg = string2Int(&s,L_CONST);

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
			filter_rate_init(&inst->filt_data_struct.prev);
			break;
		}
		case OP_ABS_DIFF_ANGLE: {
			inst->comp_const.d = (double) constant;
			inst->filt_data_struct.diff_angle = (double) arg;
			break;
		}
		case OP_MOVAVG: {
			inst->comp_const.d = (double) constant;
			inst->filt_data_struct.movavg = filter_movavg_init((uint16_t)arg);
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
void parse_inst_pt(char* bin) {
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
void parse_interval_pt(char* bin) {
	int PC = 0;
	char *pch;
	char line[L_INTERVAL];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_INTERVAL);

	while ( pch != NULL ) {
		decode_interval(line, &interval_mem_pt[PC]);
		PC++;
		memcpy(line, pch + 1, L_INTERVAL);
		pch = (char *) memchr(pch + 1, '\n', strlen(pch));
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
void parse_at(char *bin)
{
	int PC = 0;
	char *pch;
	char line[L_AT_INSTRUCTION];

	pch = (char *) memchr(bin, '\n', strlen(bin));
	if(pch != NULL)
		memcpy(line, bin, L_AT_INSTRUCTION);

	while ( pch != NULL ) {
		decode_at_instr(line, &at_instructions[PC]);
		PC++;
		memcpy(line, pch + 1, L_AT_INSTRUCTION);
		pch = (char *) memchr(pch + 1, '\n', strlen(pch));
	}

	num_instr = PC; // set number of AT instructions
}

void parse_file(char *filename, parser_t p_type)
{
	long size;
	FILE *file = fopen (filename, "r");
	if ( file != NULL ) {
		fseek(file, 0, SEEK_END);
		size = ftell(file);
		rewind(file);

		char *bin = (char *) malloc(sizeof(char) * size);
		if(fread(bin, 1, size, file) != size)
			perror (filename); // error reading from file

		switch(p_type){
			case P_FTI: parse_inst_ft(bin); break;
			case P_FTM: parse_interval_ft(bin); break;
			case P_SCQ: parse_scq_size(bin); break;
			case P_PTM: parse_inst_ft(bin); break;
			case P_PTI: parse_interval_pt(bin); break;
			case P_AT:  parse_at(bin); break;
			default: perror (filename);
		}
		fclose (file);
		free(bin);
	} else {
		perror (filename); // why didn't the file open?
	}
}
