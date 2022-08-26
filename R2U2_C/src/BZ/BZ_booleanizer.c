#include <stdio.h>

#include "BZ_booleanizer.h"
#include "BZ_operations.h"

void bz_booleanizer_init(bz_booleanizer_t *bz, uint32_t num_instr)
{
    uint32_t i;

    bz->num_instr = num_instr;

    for(i = 0; i < N_SIGS; ++i) {
        bz->sig_vector[i].b = false;
    }

    for(i = 0; i < N_BZ; ++i) {
        bz->bz_vector[i] = false;
    }
}

void bz_booleanizer_update(bz_booleanizer_t *bz)
{
    uint32_t i;
    for(i = 0; i < bz->num_instr; ++i) {
        bz_decode[bz->instructions[i].opcode](bz,bz->instructions[i].param);
    }
}