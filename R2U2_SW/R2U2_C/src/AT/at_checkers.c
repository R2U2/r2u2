#include "at_checkers.h"
#include "at_operations.h"
#include "at_globals.h"

#include <stdlib.h>

#include "filters/filter_rate.h"
#include "filters/filter_movavg.h"

void
at_checkers_init()
{
	/*
	 * Hard coding AT instructions for now; need to implement proper
	 * parsing of the input file on the python end and create a binary
	 * format that is then read from here
	*/

	num_instr = 4;

	instructions[0].comp = EQ;
	instructions[0].opcode = OP_BOOL;
	instructions[0].sig_addr = 0;
	instructions[0].atom_addr = 0;

	instructions[1].comp = LT;
	instructions[1].opcode = OP_INT;
	instructions[1].sig_addr = 1;
	instructions[1].comp_const.i = 8;
	instructions[1].atom_addr = 1;

	instructions[2].comp = GT;
	instructions[2].opcode = OP_ABS_DIFF_ANGLE;
	instructions[2].sig_addr = 2;
	instructions[2].filt_data_struct.diff_angle = 90;
	instructions[2].comp_const.d = 30;
	instructions[2].atom_addr = 2;

	instructions[3].comp = GT;
	instructions[3].opcode = OP_MOVAVG;
	instructions[3].sig_addr = 3;
	instructions[3].comp_const.d = 3;
	instructions[3].atom_addr = 3;

	uint8_t i;
	for(i = 0; i < num_instr; i++) {
		switch(instructions[i].opcode) {
			case OP_MOVAVG: {
				uint8_t filt_size = 3;
				instructions[i].filt_data_struct.movavg = filter_movavg_init(filt_size);
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
