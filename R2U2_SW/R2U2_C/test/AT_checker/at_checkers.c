#include "at_checkers.h"
#include "at_operations.h"
#include "at_globals.h"

#include <stdlib.h>

#include "../../src/AT/filter_rate.h"
#include "../../src/AT/filter_movavg.h"

void 
at_checkers_init()
{
	uint8_t i;
	for(i = 0; i < num_instr; i++) {
		switch(instructions[i].opcode) {
			case OP_MOVAVG: { 
				uint8_t filt_size = 3;
				instructions[i].filt_data_struct.movavg = 
					filter_movavg_init(filt_size);
				break;
			}
			case OP_RATE: {	
				filter_rate_init(instructions[i].filt_data_struct.prev);
				break;
			}
			default: {
				break;
			}
		}
	}
}

void 
at_checkers_update()
{
	uint8_t i;
	for(i = 0; i < num_instr; i++) {
		decode[instructions[i].opcode](instructions[i]);
	}
}

void 
at_checkers_free()
{
	uint8_t i;
	for(i = 0; i < num_instr; i++) {
		switch(instructions[i].opcode) {
			case OP_MOVAVG: { 
				filter_movavg_free(instructions[i].filt_data_struct.movavg);
				break;
			}
			default: {
				break;
			}
		}
	}
}
