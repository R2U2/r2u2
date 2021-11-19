#include "at_checkers.h"
#include "at_operations.h"
#include "at_globals.h"

#include <stdlib.h>

#if R2U2_AT_Extra_Filters
#include "extra_filters/filter_rate.h"
#include "extra_filters/filter_movavg.h"
#endif

#include "parse.h"

#ifndef CONFIG
void AT_config(const char *filename)
{
	parse_at_file(filename);
}
#else
void AT_config(const char *filename)
{
	parse_at_bin(at_bin);
}
#endif

void AT_init(void)
{
	return;
}

void AT_update(void)
{
	R2U2_DEBUG_PRINT("\n\nAT Update\n");
	uint32_t i;
	for(i = 0; i < num_instr; i++) {
		R2U2_DEBUG_PRINT("\tAT Inst: %d\n", i);
		R2U2_DEBUG_PRINT("\tSig# %d -> Filt# %d-> Comp# %d -> Atom#: %d\n",
		                 at_instructions[i].sig_addr, at_instructions[i].filter,
		                 at_instructions[i].cond, at_instructions[i].atom_addr);
		decode[at_instructions[i].filter](at_instructions+i);
	R2U2_DEBUG_PRINT("\n\n");
	}
}

void AT_free()
{
	#if R2U2_AT_Extra_Filters
	uint32_t i;
	for(i = 0; i < num_instr; i++) {
		filt_data_struct_t filter_data_struct = at_instructions[i].filt_data_struct;
		switch(at_instructions[i].filter) {
			case OP_BOOL: break;
			case OP_INT: break;
			case OP_DOUBLE: break;
			case OP_RATE: break;
			case OP_ABS_DIFF_ANGLE: break;
			case OP_MOVAVG: filter_movavg_free(filter_data_struct.movavg);
											break;
			default: break;
		}

	}
	#endif
}
