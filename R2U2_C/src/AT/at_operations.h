#ifndef OPERATIONS_H
#define OPERATIONS_H

#include <stdint.h>

#include "at_instruction.h"

#ifdef R2U2_AT_ExtraFilters
void op_abs_diff_angle(at_instruction_t *);
void op_movavg(at_instruction_t *);
void op_rate(at_instruction_t *);
#endif

void op_bool(at_instruction_t *);
void op_int(at_instruction_t *);
void op_double(at_instruction_t *);

void op_error(at_instruction_t *);
extern void (*decode[])(at_instruction_t *);

#endif