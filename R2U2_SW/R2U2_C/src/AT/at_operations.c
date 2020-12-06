#include "at_operations.h"

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "at_globals.h"
#include "filters/filter_abs_diff_angle.h"
#include "filters/filter_rate.h"
#include "filters/filter_movavg.h"
#include "../TL/TL_observers.h"

void op_abs_diff_angle(at_instruction_t *instr)
{
	double signal;
	sscanf(signals_vector[instr->sig_addr], "%lf", &signal);
	double diff_angle = (double)abs_diff_angle(signal, instr->filt_data_struct.diff_angle);

	atomics_vector[instr->atom_addr] =
		compare_double[instr->comp](diff_angle, instr->comp_const.d);

	AT_LOG("%hhu", atomics_vector[instr->atom_addr]);
}

void op_movavg(at_instruction_t *instr)
{
	int32_t signal;
	sscanf(signals_vector[instr->sig_addr], "%d", &signal);
	filter_movavg_update_data(instr->filt_data_struct.movavg, signal);
	double avg = filter_movavg_get(instr->filt_data_struct.movavg);

	atomics_vector[instr->atom_addr] =
		compare_double[instr->comp](avg, instr->comp_const.d);

	AT_LOG("%hhu", atomics_vector[instr->atom_addr]);
}

void op_rate(at_instruction_t *instr)
{
	double signal;
	sscanf(signals_vector[instr->sig_addr], "%lf", &signal);

	double rate = filter_rate_update_data(signal, &instr->filt_data_struct.prev);
	atomics_vector[instr->atom_addr] =
		compare_double[instr->comp](rate, instr->comp_const.d);

	AT_LOG("%hhu", atomics_vector[instr->atom_addr]);
}

void op_bool(at_instruction_t *instr)
{
	bool signal;
	sscanf(signals_vector[instr->sig_addr], "%hhu", &signal);

	atomics_vector[instr->atom_addr] =
		compare_int[instr->comp](signal, instr->comp_const.i);

	AT_LOG("%hhu", atomics_vector[instr->atom_addr]);
}

void op_int(at_instruction_t *instr)
{
	int32_t signal;
	sscanf(signals_vector[instr->sig_addr], "%d", &signal);

	atomics_vector[instr->atom_addr] =
		compare_int[instr->comp](signal, instr->comp_const.i);

	AT_LOG("%hhu", atomics_vector[instr->atom_addr]);
}

void op_double(at_instruction_t *instr)
{
	double signal;
	sscanf(signals_vector[instr->sig_addr], "%lf", &signal);

	atomics_vector[instr->atom_addr] =
		compare_double[instr->comp](signal, instr->comp_const.d);

	AT_LOG("%hhu", atomics_vector[instr->atom_addr]);
}

void op_error(at_instruction_t *instr)
{
	printf("Error: invalid opcode\n");
}

void (*decode[])(at_instruction_t *) = {op_error,
																				op_bool,
																				op_int,
																				op_double,
																				op_rate,
																				op_abs_diff_angle,
									  										op_movavg};
