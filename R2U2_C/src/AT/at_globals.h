#ifndef AT_GLOBALS_H
#define AT_GLOBALS_H

#include "R2U2.h"

#include <stdint.h>

#include "at_instruction.h"
#include "at_compare.h"
#include "at_operations.h"

typedef char *signals_vector_t[N_SIGS];
typedef at_instruction_t instructions_t[N_AT];

/* similar to TL_observers? */
extern signals_vector_t signals_vector;
extern instructions_t at_instructions;
extern uint32_t num_instr;

/* For no file handling option */
extern char *at_bin;

#endif
