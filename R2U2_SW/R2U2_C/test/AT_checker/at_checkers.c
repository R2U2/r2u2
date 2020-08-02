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
			case OP_RATE: {	
				break;
			}
			case OP_MOVAVG: { 
				uint8_t filt_size = 3;
				int32_t *filt_space = (int32_t *)malloc(sizeof(int32_t)*filt_size);
				circBuf_t *filt_cb = (circBuf_t *)malloc(sizeof(circBuf_t));
				filt_cb->buffer = filt_space;
				filt_cb->head = 0;
				filt_cb->tail = 0;
				filt_cb->maxLen = filt_size;
				instructions[i].filt_data_struct.movavg = 
					(movAvg_t *)malloc(sizeof(movAvg_t));
				instructions[i].filt_data_struct.movavg->pCb = filt_cb;
				instructions[i].filt_data_struct.movavg->sum = 0; 
				instructions[i].filt_data_struct.movavg->avg = 0; 
				instructions[i].filt_data_struct.movavg->num_of_elements = 0;
				instructions[i].filt_data_struct.movavg->size = filt_size;
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
	return;
}
