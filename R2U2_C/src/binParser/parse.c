#include "R2U2.h"
#include "parse.h"

#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>

#include "TL_observers.h"
#include "TL_queue_ft.h"

#include "at_instruction.h"
#include "at_globals.h"

#if R2U2_AT_Extra_Filters
#include "extra_filters/filter_rate.h"
#include "extra_filters/filter_movavg.h"
#endif

// TODO: Why is this limited to int? It could be grater
// Also, this should be typed punned
static inline int string2Int(char** char_vec, int len) {
	int op = 0;
	for(int i=0;i<len;i++) {
		op = op<<1 | (*(*char_vec+i)-'0');
	}
	*char_vec += len; //skip the data that has been read
	return op;
}

static void decode_inst(char* s, instruction_t* inst) {
	//1. operant code, 5 bits
	inst->opcode = string2Int(&s,L_OPC);

	//2. op1, 10 bits. First 2 bit is the input type
	inst->op1.opnd_type = string2Int(&s,2);
	inst->op1.value = (uint8_t)string2Int(&s,L_OP-2);

	//3. op2, 10 bits. First 2 bit is the input type
	inst->op2.opnd_type = string2Int(&s,2);
	inst->op2.value = (uint8_t)string2Int(&s,L_OP-2);

	//4. time stamp  address, 8 bits
	inst->adr_interval = (uint8_t)string2Int(&s,L_INTVL);

	//5. scratch? 7 bits (seems for Bayesian network)
	inst->scratch = (uint8_t)string2Int(&s,L_SCRATCH);
}

static void decode_interval(char* s, interval_t* interval) {
	//1. lower bound, time stamp bits
	interval->lb = (interval_bound_t)string2Int(&s,L_INTERVAL);

	//2. upper bound, time stamp bits
	interval->ub = (interval_bound_t)string2Int(&s,L_INTERVAL);
}

static void decode_scq_size(char* s, addr_SCQ_t* addr) {
	//1. start address
	addr->start_addr = (uint16_t)string2Int(&s,L_SCQ_ADDRESS);

	//2. end address
	addr->end_addr = (uint16_t)string2Int(&s,L_SCQ_ADDRESS);
}

static void decode_at_instr(char* s, at_instruction_t* inst) {
	// 1. index to place final atomic value
	inst->atom_addr = (uint8_t)string2Int(&s,L_ATOMIC_ADDR);

	// 2. type of filter to apply to signal
	inst->filter = string2Int(&s,L_FILTER);

	// 3. type of comparison operator to apply
	inst->cond = string2Int(&s,L_COMP);

	// 4. is the comparison value a signal?
	inst->comp_is_sig = string2Int(&s,1);

	// 5. value of constant/signal to compare to filtered signal
	int comp = string2Int(&s,L_NUM);

	// 6. signal we're considering
	inst->sig_addr = (uint8_t)string2Int(&s,L_SIG_ADDR);

	// 7. extra filter argument
	int arg = string2Int(&s,L_NUM);

	if(inst->comp_is_sig)
		inst->comp.s = (uint8_t) comp;

	switch(inst->filter) {		
		case OP_BOOL:
		{
			if(!inst->comp_is_sig)
				inst->comp.b = (bool) comp;
			break;
		}
		case OP_INT:
		{
			if(!inst->comp_is_sig)
				inst->comp.i = (int32_t) comp;
			break;
		}
		case OP_DOUBLE:
		{
			if(!inst->comp_is_sig)
				inst->comp.d = (double) comp;
			inst->filt_data_struct.epsilon = arg;
			break;
		}
		#if R2U2_AT_Extra_Filters
		case OP_RATE:
		{
			if(!inst->comp_is_sig)
				inst->comp.d = (double) comp;
			inst->filt_data_struct.prev = 0;
			break;
		}
		case OP_ABS_DIFF_ANGLE:
		{
			if(!inst->comp_is_sig)
				inst->comp.d = (double) comp;
			inst->filt_data_struct.diff_angle = (double) arg;
			break;
		}
		case OP_MOVAVG:
		{
			if(!inst->comp_is_sig)
				inst->comp.d = (double) comp;
			inst->filt_data_struct.movavg = filter_movavg_init((uint16_t)arg);
			break;
		}
		#endif
		#if R2U2_AT_Signal_Sets
		case OP_EXACTLY_ONE_OF:
		{
			// set_addr is stored in instr.set_addr
			if(!inst->comp_is_sig)
				inst->comp.b = (bool) comp;
			break;
		}
		case OP_NONE_OF:
		{
			// set_addr is stored in instr.set_addr
			if(!inst->comp_is_sig)
				inst->comp.b = (bool) comp;
			break;
		}
		case OP_ALL_OF:
		{
			// set_addr is stored in instr.set_addr
			if(!inst->comp_is_sig)
				inst->comp.b = (bool) comp;
			break;
		}
		#endif
		default: break;
	}
}

//------------------------------------------------------------------------------
// Future Time Instruction Parser
//------------------------------------------------------------------------------
#ifndef CONFIG
void parse_inst_ft_file(const char* filename) {
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
#else
void parse_inst_ft_bin(const char* bin) {
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
#endif
//------------------------------------------------------------------------------
// Past Time Instruction Parser
//------------------------------------------------------------------------------
#ifndef CONFIG
void parse_inst_pt_file(const char* filename) {
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
#else
void parse_inst_pt_bin(const char* bin) {
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
#endif
//------------------------------------------------------------------------------
// Future-Time Interval Parser
//------------------------------------------------------------------------------
#ifndef CONFIG
void parse_interval_ft_file(const char* filename) {
	int PC = 0;
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
#else
void parse_interval_ft_bin(const char* bin) {
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
#endif
//------------------------------------------------------------------------------
// Past-Time Interval Parser
//------------------------------------------------------------------------------
#ifndef CONFIG
void parse_interval_pt_file(const char* filename) {
	int PC = 0;
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
#else
void parse_interval_pt_bin(const char* bin) {
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
#endif
//------------------------------------------------------------------------------
// SCQ Parser (only Future-Time; Past-Time doesn't use SCQs)
//------------------------------------------------------------------------------
#ifndef CONFIG
void parse_scq_size_file(const char* filename) {
	int PC = 0;
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
#else
void parse_scq_size_bin(const char* bin) {
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
#endif
//------------------------------------------------------------------------------
// AT Parser
//------------------------------------------------------------------------------
#ifndef CONFIG
void parse_at_file(const char *filename)
{
	uint8_t PC = 0;
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
#else
void parse_at_bin(const char *bin)
{
	uint8_t PC = 0;
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
#endif
