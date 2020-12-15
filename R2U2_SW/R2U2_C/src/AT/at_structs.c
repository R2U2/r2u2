#include <stdint.h>
	#include <stdbool.h>

	#include "at_instruction.h"
	#include "at_globals.h"
	#include "filters/filter_rate.h"
	#include "filters/filter_movavg.h"

	void populate_at_instr() {
	at_instructions[0].atom_addr = 0;
at_instructions[0].filter = 1;
at_instructions[0].comp_const.b = (bool) 1;
at_instructions[0].sig_addr = 0;
at_instructions[0].comp = 0;

at_instructions[1].atom_addr = 1;
at_instructions[1].filter = 2;
at_instructions[1].comp_const.i = 2299;
at_instructions[1].sig_addr = 1;
at_instructions[1].comp = 4;

at_instructions[2].atom_addr = 2;
at_instructions[2].filter = 3;
at_instructions[2].comp_const.d = 8824;
at_instructions[2].sig_addr = 2;
at_instructions[2].comp = 4;

at_instructions[3].atom_addr = 3;
at_instructions[3].filter = 5;
at_instructions[3].comp_const.d = 86;
at_instructions[3].filt_data_struct.diff_angle = -63;
at_instructions[3].sig_addr = 3;
at_instructions[3].comp = 2;

at_instructions[4].atom_addr = 4;
at_instructions[4].filter = 4;
at_instructions[4].comp_const.d = 2977;
at_instructions[4].sig_addr = 4;
at_instructions[4].comp = 5;

at_instructions[5].atom_addr = 5;
at_instructions[5].filter = 6;
at_instructions[5].comp_const.d = -4809;
at_instructions[5].filt_data_struct.movavg = filter_movavg_init((uint16_t)2739);
at_instructions[5].sig_addr = 5;
at_instructions[5].comp = 3;

num_instr = 6;
}