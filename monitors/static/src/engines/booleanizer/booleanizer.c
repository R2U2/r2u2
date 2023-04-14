#include <stdio.h>

#include "booleanizer.h"

r2u2_status_t r2u2_bz_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_bz_instruction_t *instr)
{
    uint32_t i1, i2, i3;
    float f1, f2, f3;
    bool b;

    switch(instr->opcode) {
        case R2U2_BZ_OP_NONE: 
            break;
        /* Load */
        case R2U2_BZ_OP_ILOAD:
            i1 = bz.instructions[i].param.i; // signal idx
            i2 = bz.sig_vector[i1].i;
            bz_stack_ipush(&bz.stack, i2);
            break;
        case R2U2_BZ_OP_FLOAD:
            i1 = bz.instructions[i].param.i; // signal idx
            f1 = bz.sig_vector[i1].f;
            bz_stack_fpush(&bz.stack, f1);
            break;
        /* Bitwise */
        case R2U2_BZ_OP_BWNEG:
            i1 = bz_stack_pop(&bz.stack).i;
            b = ~i1;
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_BWAND:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 & i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_BWOR:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 | i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_BWXOR:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 ^ i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        /* Equality */
        case R2U2_BZ_OP_IEQ:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 == i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_FEQ:
            f3 =bz.instructions[i]. param.f;
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 > f2) ? (f1 - f2 <= f3) : (f2 - f1 <= f3);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_INEQ:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 != i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_FNEQ:
            f3 = bz.instructions[i].param.f;
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 > f2) ? (f1 - f2 > f3) : (f2 - f1 > f3);
            bz_stack_bpush(&bz.stack, b);
            break;
        /* Inequality */
        case R2U2_BZ_OP_IGT:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 > i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_FGT:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 > f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_IGTE:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 >= i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_FGTE:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 >= f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_ILT:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 < i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_FLT:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 < f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_ILTE:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            b = (i1 <= i2);
            bz_stack_bpush(&bz.stack, b);
            break;
        case R2U2_BZ_OP_FLTE:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            b = (f1 <= f2);
            bz_stack_bpush(&bz.stack, b);
            break;
        /* Arithmetic */
        case R2U2_BZ_OP_INEG:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = -i1;
            bz_stack_ipush(&bz.stack, i2);
            break;
        case R2U2_BZ_OP_FNEG:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = -f1;
            bz_stack_fpush(&bz.stack, f2);
            break;
        case R2U2_BZ_OP_IADD:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 + i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case R2U2_BZ_OP_FADD:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 + f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        case R2U2_BZ_OP_ISUB:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 - i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case R2U2_BZ_OP_FSUB:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 - f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        case R2U2_BZ_OP_IMUL:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 * i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case R2U2_BZ_OP_FMUL:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 * f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        case R2U2_BZ_OP_IDIV:
            i1 = bz_stack_pop(&bz.stack).i;
            i2 = bz_stack_pop(&bz.stack).i;
            i3 = i1 / i2;
            bz_stack_ipush(&bz.stack,i3);
            break;
        case R2U2_BZ_OP_FDIV:
            f1 = bz_stack_pop(&bz.stack).f;
            f2 = bz_stack_pop(&bz.stack).f;
            f3 = f1 / f2;
            bz_stack_fpush(&bz.stack,f3);
            break;
        /* Auxiliary */
        case R2U2_BZ_OP_AUX1:
        case R2U2_BZ_OP_AUX2:
        case R2U2_BZ_OP_AUX3:
        case R2U2_BZ_OP_AUX4:
        default:
            break;
    }

    return R2U2_OK;
}