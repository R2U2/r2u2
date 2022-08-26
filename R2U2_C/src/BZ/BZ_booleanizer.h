#ifndef BZ_BOOLEANIZER_H
#define BZ_BOOLEANIZER_H

#include "BZ_stack.h"

#define MAX_SIGS 4
#define MAX_BZ 4

/*
 * A booleanizer is an engine that converts input signals
 * into booleans according to the given specification. It functions
 * as a stack machine by using a stack to keep track of its internal
 * state. 
 */
typedef struct bz_booleanizer {
    bz_stack_t stack;
    bz_instruction_t instructions[N_BZ_INSTR];
    uint32_t num_instr;
    char *sig_vector[MAX_SIGS];
    bool bz_vector[MAX_BZ];
} bz_booleanizer_t;

void bz_booleanizer_init(bz_booleanizer_t *);
void bz_booleanizer_update(bz_booleanizer_t *);

#endif