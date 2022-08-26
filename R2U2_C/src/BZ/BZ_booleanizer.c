#include <stdio.h>

#include "BZ_booleanizer.h"

void bz_booleanizer_init(bz_booleanizer_t *bz, uint32_t num_instr)
{
    uint32_t i;

    bz->num_instr = 0;

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
        printf("hello world!\n");
    }
}