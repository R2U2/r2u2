#ifndef BZ_BOOLEANIZER_H
#define BZ_BOOLEANIZER_H

#include <stdint.h>
#include <stdbool.h>

#include "R2U2.h"
#include "bz_stack.h"
#include "bz_instruction.h"

#define MAX_BZ_INSTR 256
#define MAX_BZ 4
#define MAX_REG 8

/*
 * A booleanizer is an engine that converts input signals
 * into booleans according to the given specification. It functions
 * as a stack machine by using a stack to keep track of its internal
 * state. 
 */
typedef struct bz_booleanizer {
    bz_stack_t stack;
    bz_val_t reg[MAX_REG];
    uint32_t cur_reg;
    bz_instruction_t instructions[MAX_BZ_INSTR];
    uint32_t num_instr;
    bz_val_t sig_vector[N_SIGS];
    bool bz_vector[MAX_BZ];
} bz_booleanizer_t;

typedef char *signals_vector_t[N_SIGS];

extern bz_booleanizer_t bz;
extern signals_vector_t signals_vector;

void bz_init(void);
void bz_update(void);
void bz_execute(uint32_t);

bool bz_opcode_has_param(bz_opcode_t);

#endif