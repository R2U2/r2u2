#include <stdio.h>

#include "booleanizer.h"

r2u2_status_t r2u2_bz_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_bz_instruction_t *instr)
{
    r2u2_bool b;
    r2u2_int i1, i2, i3;
    r2u2_float f1, f2, f3;

    switch(instr->opcode) {
        case R2U2_BZ_OP_NONE: 
            break;
        /* Load */
        case R2U2_BZ_OP_ILOAD:
            sscanf((*(monitor->signal_vector))[instr->param.bz_int], "%d", &i1);
            (*monitor->value_buffer)[instr->addr].i = i1;
            R2U2_DEBUG_PRINT("\tBZ LOAD\n");
            R2U2_DEBUG_PRINT("\tb%d = %d (b%d)\n", instr->addr, i1, instr->param.bz_int);
            break;
        case R2U2_BZ_OP_FLOAD:
            sscanf((*(monitor->signal_vector))[instr->param.bz_int], "%f", &f1);
            (*monitor->value_buffer)[instr->addr].f = f1;
            break;
        /* Bitwise */
        case R2U2_BZ_OP_BWNEG:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = ~i1;
            (*monitor->value_buffer)[instr->addr].i = i2;
            break;
        case R2U2_BZ_OP_BWAND:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 & i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        case R2U2_BZ_OP_BWOR:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 | i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        case R2U2_BZ_OP_BWXOR:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 ^ i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        /* Equality */
        case R2U2_BZ_OP_IEQ:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            b = i1 == i2;
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        case R2U2_BZ_OP_FEQ:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            b = (f1 > f2) ? (f1 - f2 < R2U2_FLOAT_EPSILON) : (f2 - f1 < R2U2_FLOAT_EPSILON);
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        case R2U2_BZ_OP_INEQ:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            b = i1 != i2;
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        case R2U2_BZ_OP_FNEQ:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            b = !((f1 > f2) ? (f1 - f2 < R2U2_FLOAT_EPSILON) : (f2 - f1 < R2U2_FLOAT_EPSILON));
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        /* Inequality */
        case R2U2_BZ_OP_IGT:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            b = i1 > i2;
            (*monitor->value_buffer)[instr->addr].b = b;
            R2U2_DEBUG_PRINT("\tBZ GT\n");
            R2U2_DEBUG_PRINT("\tb%d = %d > %d (b%d > b%d)\n", instr->addr, 
                (*monitor->value_buffer)[instr->param.bz_addr[0]].i, 
                (*monitor->value_buffer)[instr->param.bz_addr[1]].i,
                instr->param.bz_addr[0], instr->param.bz_addr[1]);
            break;
        case R2U2_BZ_OP_FGT:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            b = f1 > f2;
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        case R2U2_BZ_OP_IGTE:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            b = i1 >= i2;
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        case R2U2_BZ_OP_ILT:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            b = i1 < i2;
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        case R2U2_BZ_OP_FLT:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            b = f1 < f2;
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        case R2U2_BZ_OP_ILTE:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            b = i1 <= i2;
            (*monitor->value_buffer)[instr->addr].b = b;
            break;
        /* Arithmetic */
        case R2U2_BZ_OP_INEG:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = -i1;
            (*monitor->value_buffer)[instr->addr].i = i2;
            break;
        case R2U2_BZ_OP_FNEG:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = -f1;
            (*monitor->value_buffer)[instr->addr].f = f2;
            break;
        case R2U2_BZ_OP_IADD:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 + i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        case R2U2_BZ_OP_FADD:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            f3 = f1 + f2;
            (*monitor->value_buffer)[instr->addr].f = f3;
            break;
        case R2U2_BZ_OP_ISUB:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 - i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        case R2U2_BZ_OP_FSUB:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            f3 = f1 - f2;
            (*monitor->value_buffer)[instr->addr].f = f3;
            break;
        case R2U2_BZ_OP_IMUL:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 * i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        case R2U2_BZ_OP_FMUL:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            f3 = f1 * f2;
            (*monitor->value_buffer)[instr->addr].f = f3;
            break;
        case R2U2_BZ_OP_IDIV:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 / i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        case R2U2_BZ_OP_FDIV:
            f1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].f;
            f2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].f;
            f3 = f1 / f2;
            (*monitor->value_buffer)[instr->addr].f = f3;
            break;
        case R2U2_BZ_OP_MOD:
            i1 = (*monitor->value_buffer)[instr->param.bz_addr[0]].i;
            i2 = (*monitor->value_buffer)[instr->param.bz_addr[1]].i;
            i3 = i1 % i2;
            (*monitor->value_buffer)[instr->addr].i = i3;
            break;
        default:
            break;
    }

    if(instr->store) {
        monitor->atomic_buffer[instr->at_addr] = &(*monitor->value_buffer)[instr->addr].b;
        R2U2_DEBUG_PRINT("\ta%d = %hhu (b%d)\n", instr->at_addr, (*monitor->value_buffer)[instr->addr].b, instr->addr);
    }

    return R2U2_OK;
}