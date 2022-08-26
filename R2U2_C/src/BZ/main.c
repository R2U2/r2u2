#include <stdint.h>

#include "BZ_booleanizer.h"
#include "BZ_instruction.h"

#define DEFAULT_BZ_INSTR 64

void main()
{
    bz_booleanizer_t bz;

    bz_booleanizer_init(&bz,4);

    bz.instructions[0].opcode = ILOAD;
    bz.instructions[0].param.i = 0;
    bz.instructions[1].opcode = ILOAD;
    bz.instructions[1].param.i = 1;
    bz.instructions[2].opcode = IEQ;
    bz.instructions[2].param.i = 0;
    bz.instructions[3].opcode = STORE;
    bz.instructions[3].param.i = 0;

    bz.sig_vector[0].i = 7;
    bz.sig_vector[1].i = 7;

    bz_booleanizer_update(&bz);

}