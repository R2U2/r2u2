
#include "BZ_booleanizer.h"

void bz_booleanizer_init(bz_booleanizer_t *bz, uint32_t num_instr)
{
    uint32_t i;

    bz->num_instr = 0;

    for(i = 0; i < N_BZ_INSTR) {
        bz->instructions[i] = {NONE,0};
    }

    for(i = 0; i < N_SIGS) {
        bz->sig_vector = "";
    }

    for(i = 0; i < N_BZ) {
        bz->bz_vector = false;
    }
}

void bz_booleanizer_update()
{
    uint32_t i;
    for(i = 0; i < bz.num_instr; ++i) {

    }
}