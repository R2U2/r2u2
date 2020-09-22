#include "at_operations.h"

#include <stdio.h>
#include <stdint.h>
#include "at_globals.h"
#include "filters/filter_abs_diff_angle.h"
#include "filters/filter_rate.h"
#include "../TL/TL_observers.h"

void op_abs_diff_angle(at_instruction_t instr)
{
	double diff_angle = abs_diff_angle(signals_vector[instr.sig_addr].d,
		instr.filt_data_struct.diff_angle);
	atomics_vector[instr.atom_addr] =
		compare_double[instr.comp](diff_angle, instr.comp_const.d);
}

void op_movavg(at_instruction_t instr)
{
	filter_movavg_update_data(instr.filt_data_struct.movavg,
		signals_vector[instr.sig_addr].i);
	double avg = (double)filter_movavg_get(instr.filt_data_struct.movavg);
	atomics_vector[instr.atom_addr] =
		compare_double[instr.comp](avg, instr.comp_const.d);
}

void op_rate(at_instruction_t instr)
{
	double rate = filter_rate_update_data(signals_vector[instr.sig_addr].d,
										  instr.filt_data_struct.prev);
	atomics_vector[instr.atom_addr] =
		compare_double[instr.comp](rate, instr.comp_const.d);
}

void op_bool(at_instruction_t instr)
{
	atomics_vector[instr.atom_addr] = signals_vector[instr.sig_addr].b;
}

void op_int(at_instruction_t instr)
{
	atomics_vector[instr.atom_addr] =
		compare_int[instr.comp](signals_vector[instr.sig_addr].i,
								instr.comp_const.i);
}

void op_double(at_instruction_t instr)
{
	atomics_vector[instr.atom_addr] =
		compare_double[instr.comp](signals_vector[instr.sig_addr].d,
								   instr.comp_const.d);
}

void (*decode[])(at_instruction_t) = {op_abs_diff_angle,
									  op_movavg,
									  op_rate,
									  op_bool,
									  op_int,
									  op_double};
