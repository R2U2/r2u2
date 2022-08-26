#include <stdint.h>

#include "BZ_booleanizer.h"
#include "BZ_instruction.h"

#define DEFAULT_BZ_INSTR 64

void main()
{
    bz_stack_t stack;

    bz_instruction_t instr[DEFAULT_BZ_INSTR] = {
        {ILOAD,0},
        {ILOAD,1},
        {IEQ,0},
        {STORE,0}
    };

    bz_booleanizer_t bz;

    bz_booleanizer_init(&bz,8);

    bz.instructions = instr;
    

}