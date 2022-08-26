#ifndef BZ_GLOBALS_H
#define BS_GLOBALS_H

typedef char *signals_vector_t[N_SIGS];
typedef at_instruction_t instructions_t[N_AT];

/* similar to TL_observers? */
extern signals_vector_t signals_vector;
extern instructions_t at_instructions;
extern uint32_t num_instr;

/* For no file handling option */
extern char *at_bin;

#endif