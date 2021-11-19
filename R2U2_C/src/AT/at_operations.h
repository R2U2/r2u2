#ifndef OPERATIONS_H
#define OPERATIONS_H

#include <stdint.h>

#include "R2U2.h"

#include "at_instruction.h"

#if R2U2_AT_Extra_Filters
void op_abs_diff_angle(at_instruction_t *);
void op_movavg(at_instruction_t *);
void op_rate(at_instruction_t *);
#endif

#if R2U2_AT_Signal_Sets
void op_exactly_one_of(at_instruction_t *);
#endif

void op_bool(at_instruction_t *);
void op_int(at_instruction_t *);
void op_double(at_instruction_t *);

void op_error(at_instruction_t *);
extern void (*decode[])(at_instruction_t *);

#endif
