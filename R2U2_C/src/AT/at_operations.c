#include "at_operations.h"

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "at_globals.h"

#ifdef R2U2_AT_ExtraFilters
#include "filters/filter_abs_diff_angle.h"
#include "filters/filter_rate.h"
#include "filters/filter_movavg.h"
#endif

#include "../TL/TL_observers.h"

#ifdef R2U2_AT_ExtraFilters
void op_abs_diff_angle(at_instruction_t *instr)
{
	double signal;
	sscanf(signals_vector[instr->sig_addr], "%lf", &signal);
	double diff_angle = (double)abs_diff_angle(signal, instr->filt_data_struct.diff_angle);

	if(instr->comp_is_sig) {
		double comp_sig;
		sscanf(signals_vector[instr->comp.s], "%lf", &comp_sig);
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](diff_angle, comp_sig);
	} else {
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](diff_angle, instr->comp.d);
	}

	R2U2_DEBUG_PRINT("%hhu", atomics_vector[instr->atom_addr]);
}

void op_movavg(at_instruction_t *instr)
{
	int32_t signal;
	sscanf(signals_vector[instr->sig_addr], "%d", &signal);
	filter_movavg_update_data(instr->filt_data_struct.movavg, signal);
	double avg = filter_movavg_get(instr->filt_data_struct.movavg);

	if(instr->comp_is_sig) {
		double comp_sig;
		sscanf(signals_vector[instr->comp.s], "%lf", &comp_sig);
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](avg, comp_sig);
	} else {
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](avg, instr->comp.d);
	}

	R2U2_DEBUG_PRINT("%hhu", atomics_vector[instr->atom_addr]);
}

void op_rate(at_instruction_t *instr)
{
	double signal;
	sscanf(signals_vector[instr->sig_addr], "%lf", &signal);
	double rate = filter_rate_update_data(signal, &instr->filt_data_struct.prev);

	if(instr->comp_is_sig) {
		double comp_sig;
		sscanf(signals_vector[instr->comp.s], "%lf", &comp_sig);
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](rate, comp_sig);
	} else {
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](rate, instr->comp.d);
	}

	R2U2_DEBUG_PRINT("%hhu", atomics_vector[instr->atom_addr]);
}
#endif

void op_bool(at_instruction_t *instr)
{
	bool signal;
	sscanf(signals_vector[instr->sig_addr], "%hhu", &signal);

	if(instr->comp_is_sig) {
		bool comp_sig;
		sscanf(signals_vector[instr->comp.s], "%hhu", &comp_sig);
		atomics_vector[instr->atom_addr] =
			compare_int[instr->cond](signal, comp_sig);
	} else {
		atomics_vector[instr->atom_addr] =
			compare_int[instr->cond](signal, instr->comp.b);
	}

	R2U2_DEBUG_PRINT("%hhu", atomics_vector[instr->atom_addr]);
}

void op_int(at_instruction_t *instr)
{
	int32_t signal;
	sscanf(signals_vector[instr->sig_addr], "%d", &signal);

	if(instr->comp_is_sig) {
		int32_t comp_sig;
		sscanf(signals_vector[instr->comp.s], "%d", &comp_sig);
		atomics_vector[instr->atom_addr] =
			compare_int[instr->cond](signal, comp_sig);
	} else {
		atomics_vector[instr->atom_addr] =
			compare_int[instr->cond](signal, instr->comp.i);
	}

	R2U2_DEBUG_PRINT("%hhu", atomics_vector[instr->atom_addr]);
}

void op_double(at_instruction_t *instr)
{
	double signal;
	sscanf(signals_vector[instr->sig_addr], "%lf", &signal);

	if(instr->comp_is_sig) {
		double comp_sig;
		sscanf(signals_vector[instr->comp.s], "%lf", &comp_sig);
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](signal, comp_sig);
	} else {
		atomics_vector[instr->atom_addr] =
			compare_double[instr->cond](signal, instr->comp.d);
	}

	R2U2_DEBUG_PRINT("%hhu", atomics_vector[instr->atom_addr]);
}

void op_error(at_instruction_t *instr) {
	printf("Error: invalid opcode at addr %p\n", (void *) instr);
}

void (*decode[])(at_instruction_t*) = { op_error,
    op_bool,
    op_int,
    op_double,
#ifdef R2U2_AT_ExtraFilters
    op_rate,
    op_abs_diff_angle,
    op_movavg
#endif
};
