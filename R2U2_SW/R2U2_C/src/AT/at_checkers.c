#include "at_checkers.h"
#include "at_operations.h"
#include "at_globals.h"

#include <stdlib.h>

#include "filters/filter_rate.h"
#include "filters/filter_movavg.h"
#include "parse.h"

void at_checkers_config(char *f)
{
		parse_at(f);
}

void at_checkers_init()
{
	return;
}

void at_checkers_update(uint32_t cur_time)
{
	uint8_t i;
	for(i = 0; i < num_instr; i++) {
		decode[at_instructions[i].filter](at_instructions+i);
		if(i < num_instr-1)
			AT_LOG(",");
	}
	AT_LOG("\n");
}

void at_checkers_free()
{
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
}
