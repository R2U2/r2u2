#include "at_checkers.h"
#include "at_operations.h"
#include "at_globals.h"

#include <stdlib.h>

#ifdef R2U2_AT_ExtraFilters
#include "filters/filter_rate.h"
#include "filters/filter_movavg.h"
#endif

#include "parse.h"

#ifndef CONFIG
void AT_config(char *filename)
{
	parse_at_file(filename);
}
#else
void AT_config(char *filename)
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
	uint8_t i;
	for(i = 0; i < num_instr; i++) {
		decode[at_instructions[i].filter](at_instructions+i);
		if(i < num_instr-1) R2U2_DEBUG_PRINT(",");
	}
	R2U2_DEBUG_PRINT("\n");
}

void AT_free()
{
	#ifdef R2U2_AT_ExtraFilters
	uint8_t i;
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
