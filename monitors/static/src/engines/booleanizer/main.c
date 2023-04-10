#include <stdint.h>

#include "bz_booleanizer.h"
#include "bz_instruction.h"

#define DEFAULT_BZ_INSTR 64

void main()
{
    bz_booleanizer_t bz;

    bz_booleanizer_init(&bz,6);

    bz.instructions[0].opcode = ILOAD;
    bz.instructions[0].param.i = 0;
    bz.instructions[1].opcode = ILOAD;
    bz.instructions[1].param.i = 1;
    bz.instructions[2].opcode = ILOAD;
    bz.instructions[2].param.i = 2;
    bz.instructions[3].opcode = IADD;
    bz.instructions[3].param.i = 0;
    bz.instructions[4].opcode = IEQ;
    bz.instructions[4].param.i = 0;
    bz.instructions[5].opcode = STORE;
    bz.instructions[5].param.i = 0;

    bz.sig_vector[0].i = 5;
    bz.sig_vector[1].i = 2;
    bz.sig_vector[2].i = 3;

    bz_booleanizer_update(&bz);

}