#include <stdio.h>

#include "BZ_booleanizer.h"

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
        bz_execute(bz,i);
    }
}

void bz_execute(bz_booleanizer_t *bz, uint32_t i)
{
    uint32_t i1, i2, i3;
    float f1, f2, f3;
    bool b;

    switch(bz->instructions[i].opcode) {
        /* Load/Store */
        case STORE:
            i1 = bz->instructions[i].param.i; // atomic idx
            b = bz_stack_pop(&bz->stack).b;
            // store in atomics vector
            printf("%hhu\n",b);
            break;
        case ILOAD:
            i1 = bz->instructions[i].param.i; // signal idx
            i2 = bz->sig_vector[i1].i;
            bz_stack_ipush(&bz->stack, i2);
            break;
        case FLOAD:
            i1 = bz->instructions[i].param.i; // signal idx
            f1 = bz->sig_vector[i1].f;
            bz_stack_fpush(&bz->stack, f1);
            break;
        case IITE:
        case FITE:
            break;
        /* Bitwise */
        case BWNEG:
        case BWAND:
        case BWOR:
        case BWXOR:
            break;
        /* Equality */
        case IEQ:
            i1 = bz_stack_pop(&bz->stack).i;
            i2 = bz_stack_pop(&bz->stack).i;
            b = (i1 == i2);
            bz_stack_bpush(&bz->stack, b);
            break;
        case FEQ:
            f3 =bz->instructions[i]. param.f;
            f1 = bz_stack_pop(&bz->stack).f;
            f2 = bz_stack_pop(&bz->stack).f;
            b = (f1 > f2) ? (f1 - f2 <= f3) : (f2 - f1 <= f3);
            bz_stack_bpush(&bz->stack, b);
            break;
        case INEQ:
            i1 = bz_stack_pop(&bz->stack).i;
            i2 = bz_stack_pop(&bz->stack).i;
            b = (i1 != i2);
            bz_stack_bpush(&bz->stack, b);
            break;
        case FNEQ:
            f3 = bz->instructions[i].param.f;
            f1 = bz_stack_pop(&bz->stack).f;
            f2 = bz_stack_pop(&bz->stack).f;
            b = (f1 > f2) ? (f1 - f2 > f3) : (f2 - f1 > f3);
            bz_stack_bpush(&bz->stack, b);
            break;
        /* Inequality */
        case IGT:
        case FGT:
        case IGTE:
        case FGTE:
        case ILT:
        case FLT:
        case ILTE:
        case FLTE:
        /* Arithmetic */
        case INEG:
        case FNEG:
            break;
        case IADD:
            i1 = bz_stack_pop(&bz->stack).i;
            i2 = bz_stack_pop(&bz->stack).i;
            i3 = i1 + i2;
            bz_stack_ipush(&bz->stack,i3);
            break;
        case FADD:
        case ISUB:
        case FSUB:
        case IMUL:
        case FMUL:
        case IDIV:
        case FDIV:
        /* Auxiliary */
        case AUX1:
        case AUX2:
        case AUX3:
        case AUX4:
        case NONE:
        default:
            break;
    }
}