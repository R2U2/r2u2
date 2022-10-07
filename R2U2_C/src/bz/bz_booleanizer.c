#include <stdio.h>

#include "R2U2.h"
#include "bz_booleanizer.h"
#include "../parse/parse.h"

/// Globals
bz_booleanizer_t bz;
signals_vector_t signals_vector;

void bz_init(void)
{
    uint32_t i;

    for(i = 0; i < N_SIGS; ++i) {
        bz.sig_vector[i].b = false;
    }

    for(i = 0; i < N_BZ; ++i) {
        bz.bz_vector[i] = false;
    }
}

void bz_update(void)
{
    uint32_t i;
    for(i = 0; i < bz.num_instr; ++i) {
        bz_execute(i);
    }
}

void bz_execute(uint32_t i)
{
    uint32_t i1, i2, i3;
    float f1, f2, f3;
    bool b;

    switch(bz.instructions[i].opcode) {
        case BZ_NONE: 
            break;
        /* Load/Store */
        case BZ_STORE:
            i1 = bz.instructions[i].param.i; // atomic idx
            b = bz_stack_pop(&bz.stack).b;
            // store in atomics vector
            printf("%hhu\n",b);
            break;
        case BZ_ILOAD:
            i1 = bz.instructions[i].param.i; // signal idx
            i2 = bz.sig_vector[i1].i;
            bz_stack_ipush(&bz.stack, i2);
            break;
        case BZ_FLOAD:
            i1 = bz.instructions[i].param.i; // signal idx
            f1 = bz.sig_vector[i1].f;
            bz_stack_fpush(&bz.stack, f1);
            break;
        case BZ_IITE:
        case BZ_FITE:
            break;
        /* Bitwise */
        case BZ_BWNEG:
            i1 = bz_stack_pop(&bz.stack).i;
            b = ~i1;
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_BWAND:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 & i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_BWOR:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 | i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_BWXOR:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 ^ i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        /* Equality */
        case BZ_IEQ:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 == i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_FEQ:
            f3 =bz.instructions[i]. param.f;
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 > f2) ? (f1 - f2 <= f3) : (f2 - f1 <= f3);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_INEQ:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 != i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_FNEQ:
            f3 = bz.instructions[i].param.f;
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 > f2) ? (f1 - f2 > f3) : (f2 - f1 > f3);
            bz_stack_bpush(&bz.stack, b);
            break;
        /* Inequality */
        case BZ_IGT:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 > i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_FGT:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 > f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_IGTE:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 >= i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_FGTE:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 >= f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_ILT:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 < i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_FLT:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 < f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_ILTE:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 <= i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case BZ_FLTE:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 <= f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        /* Arithmetic */
        case BZ_INEG:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = -i1;
            bz_stack_ipush(&bz.stack, i2);
            break;
        case BZ_FNEG:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = -f1;
            bz_stack_fpush(&bz.stack, f2);
            break;
        case BZ_IADD:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 + i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case BZ_FADD:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 + f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        case BZ_ISUB:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 - i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case BZ_FSUB:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 - f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        case BZ_IMUL:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 * i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case BZ_FMUL:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 * f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        case BZ_IDIV:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 / i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case BZ_FDIV:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 / f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        /* Auxiliary */
        case BZ_AUX1:
        case BZ_AUX2:
        case BZ_AUX3:
        case BZ_AUX4:
        default:
            break;
    }
}