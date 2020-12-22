#ifndef AT_GLOBALS_H
#define AT_GLOBALS_H

#include <stdint.h>
#include "at_instruction.h"
#include "at_compare.h"
#include "at_operations.h"

#define BUFFER_SIZE 256
#define MAX_AT 256
#define MAX_SIGS 256

typedef char *signals_vector_t[MAX_SIGS];
typedef at_instruction_t instructions_t[MAX_AT];

/* similar to TL_observers? */
extern signals_vector_t signals_vector;
extern instructions_t at_instructions;
extern uint8_t num_instr;

/* For no file handling option */
extern char *at_bin;

#endif
