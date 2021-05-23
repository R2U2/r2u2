#ifndef OPERATIONS_H
#define OPERATIONS_H

#include <stdint.h>

#include "at_instruction.h"

void op_abs_diff_angle(instruction_t);
void op_movavg(instruction_t);
void op_rate(instruction_t);
void op_bool(instruction_t);
void op_int(instruction_t);
void op_double(instruction_t);

extern void (*decode[])(instruction_t);

#endif
