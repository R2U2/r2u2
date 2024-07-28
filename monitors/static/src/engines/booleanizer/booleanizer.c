#include <stdio.h>
#include <math.h>

#include "booleanizer.h"

r2u2_status_t r2u2_bz_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_bz_instruction_t *instr)
{
    r2u2_bool b;
    r2u2_int i1, i2, i3;
    r2u2_float f1, f2, f3;

    // Copy to buffer to avoid alignment issues
    // TODO(bckempa): Make this optional based on bin packing switch
    r2u2_bz_instruction_t inst_buff;
    memcpy(&inst_buff, instr, sizeof(r2u2_bz_instruction_t));

    switch(inst_buff.opcode) {
        case R2U2_BZ_OP_NONE: 
            break;
        /* Load */
        case R2U2_BZ_OP_ILOAD:
            sscanf((*(monitor->signal_vector))[inst_buff.param1.bz_addr], "%d", &i1);
            (*monitor->value_buffer)[inst_buff.addr].i = i1;

            R2U2_DEBUG_PRINT("\tBZ ILOAD\n");
            R2U2_DEBUG_PRINT("\tb%d = %d (s%d)\n", inst_buff.addr, i1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_FLOAD:
            sscanf((*(monitor->signal_vector))[inst_buff.param1.bz_addr], "%lf", &f1);
            (*monitor->value_buffer)[inst_buff.addr].f = f1;

            R2U2_DEBUG_PRINT("\tBZ FLOAD\n");
            R2U2_DEBUG_PRINT("\tb%d = %lf (s%d)\n", inst_buff.addr, f1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_ICONST:
            (*monitor->value_buffer)[inst_buff.addr].i = inst_buff.param1.bz_int;

            R2U2_DEBUG_PRINT("\tBZ ICONST\n");
            R2U2_DEBUG_PRINT("\tb%d = %d\n", inst_buff.addr, inst_buff.param1.bz_int);
            break;
        case R2U2_BZ_OP_FCONST:
            (*monitor->value_buffer)[inst_buff.addr].f = inst_buff.param1.bz_float;

            R2U2_DEBUG_PRINT("\tBZ FCONST\n");
            R2U2_DEBUG_PRINT("\tb%d = %lf\n", inst_buff.addr, inst_buff.param1.bz_float);
            break;
        /* Bitwise */
        case R2U2_BZ_OP_BWNEG:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = ~i1;

            (*monitor->value_buffer)[inst_buff.addr].i = i2;

            R2U2_DEBUG_PRINT("\tBZ BW NEG\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = ~%d (~b%d)\n", inst_buff.addr,
                i2, i1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_BWAND:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 & i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ BW AND\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d & %d (b%d & b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_BWOR:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 | i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ BW OR\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d | %d (b%d | b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_BWXOR:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 ^ i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ BW XOR\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d ^ %d (b%d ^ b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        /* Equality */
        case R2U2_BZ_OP_IEQ:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            b = i1 == i2;
            
            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ IEQ\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d == %d (b%d == b%d)\n", inst_buff.addr,
                b, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FEQ:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            b = (f1 > f2) ? (f1 - f2 < R2U2_FLOAT_EPSILON) : (f2 - f1 < R2U2_FLOAT_EPSILON);

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ FEQ\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f == %f +- %f (b%d == b%d +- %f)\n", inst_buff.addr,
                b, f1, f2, R2U2_FLOAT_EPSILON, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr, R2U2_FLOAT_EPSILON);
            break;
        case R2U2_BZ_OP_INEQ:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            b = i1 != i2;

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ INEQ\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d != %d (b%d != b%d)\n", inst_buff.addr,
                b, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FNEQ:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            b = !((f1 > f2) ? (f1 - f2 < R2U2_FLOAT_EPSILON) : (f2 - f1 < R2U2_FLOAT_EPSILON));

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ FLT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f != %f +- %f (b%d != b%d +- %f)\n", inst_buff.addr,
                b, f1, f2, R2U2_FLOAT_EPSILON, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr, R2U2_FLOAT_EPSILON);
            break;
        /* Inequality */
        case R2U2_BZ_OP_IGT:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            b = i1 > i2;
            (*monitor->value_buffer)[inst_buff.addr].b = b;
            R2U2_DEBUG_PRINT("\tBZ IGT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d > %d (b%d > b%d)\n", inst_buff.addr,
                b, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FGT:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            b = f1 > f2;

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ FGT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f > %f (b%d > b%d)\n", inst_buff.addr,
                b, f1, f2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_IGTE:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            b = i1 >= i2;

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ IGTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d >= %d (b%d >= b%d)\n", inst_buff.addr,
                b, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FGTE:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            b = (f1 > f2 - R2U2_FLOAT_EPSILON);

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ FGTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f >= %f - %f (b%d == b%d - %f)\n", inst_buff.addr,
                b, f1, f2, R2U2_FLOAT_EPSILON, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr, R2U2_FLOAT_EPSILON);
            break;
        case R2U2_BZ_OP_ILT:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            b = i1 < i2;

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ ILT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d < %d (b%d < b%d)\n", inst_buff.addr,
                b, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FLT:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            b = f1 < f2;

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ FLT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f < %f (b%d < b%d)\n", inst_buff.addr,
                b, f1, f2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_ILTE:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            b = i1 <= i2;

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ ILTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d <= %d (b%d <= b%d)\n", inst_buff.addr,
                b, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FLTE:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            b = (f1 < f2 + R2U2_FLOAT_EPSILON);

            (*monitor->value_buffer)[inst_buff.addr].b = b;

            R2U2_DEBUG_PRINT("\tBZ FGTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f <= %f + %f (b%d == b%d + %f)\n", inst_buff.addr,
                b, f1, f2, R2U2_FLOAT_EPSILON, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr, R2U2_FLOAT_EPSILON);
            break;
        /* Arithmetic */
        case R2U2_BZ_OP_INEG:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = -i1;

            (*monitor->value_buffer)[inst_buff.addr].i = i2;

            R2U2_DEBUG_PRINT("\tBZ INEG\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = -%d (-b%d)\n", inst_buff.addr,
                i2, i1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_FNEG:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = -f1;

            (*monitor->value_buffer)[inst_buff.addr].f = f2;

            R2U2_DEBUG_PRINT("\tBZ FNEG\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = -%f (-b%d)\n", inst_buff.addr,
                f2, f1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_IADD:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 + i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ IADD\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d + %d (b%d + b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FADD:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            f3 = f1 + f2;

            (*monitor->value_buffer)[inst_buff.addr].f = f3;

            R2U2_DEBUG_PRINT("\tBZ FADD\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f + %f (b%d + b%d)\n", inst_buff.addr,
                f3, f1, f2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_ISUB:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 - i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ ISUB\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d - %d (b%d - b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FSUB:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            f3 = f1 - f2;

            (*monitor->value_buffer)[inst_buff.addr].f = f3;

            R2U2_DEBUG_PRINT("\tBZ FSUB\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f - %f (b%d - b%d)\n", inst_buff.addr,
                f3, f1, f2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_IMUL:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 * i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ IMUL\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d * %d (b%d * b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FMUL:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            f3 = f1 * f2;

            (*monitor->value_buffer)[inst_buff.addr].f = f3;

            R2U2_DEBUG_PRINT("\tBZ FMUL\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f * %f (b%d * b%d)\n", inst_buff.addr,
                f3, f1, f2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_IDIV:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 / i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ IDIV\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d / %d (b%d / b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FDIV:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            f3 = f1 / f2;

            (*monitor->value_buffer)[inst_buff.addr].f = f3;

            R2U2_DEBUG_PRINT("\tBZ FDIV\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f / %f (b%d / b%d)\n", inst_buff.addr,
                f3, f1, f2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_MOD:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = i1 % i2;

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ IMOD\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d %% %d (b%d %% b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_IPOW:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].i;
            i3 = pow(i1,i2);

            (*monitor->value_buffer)[inst_buff.addr].i = i3;

            R2U2_DEBUG_PRINT("\tBZ IPOW\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d pow %d (b%d pow b%d)\n", inst_buff.addr,
                i3, i1, i2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_FPOW:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (*monitor->value_buffer)[inst_buff.param2.bz_addr].f;
            f3 = pow(f1,f2);

            (*monitor->value_buffer)[inst_buff.addr].f = f3;

            R2U2_DEBUG_PRINT("\tBZ FPOW\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f pow %f (b%d pow b%d)\n", inst_buff.addr,
                f3, f1, f2, inst_buff.param1.bz_addr, inst_buff.param2.bz_addr);
            break;
        case R2U2_BZ_OP_ISQRT:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = sqrt(i1);

            (*monitor->value_buffer)[inst_buff.addr].i = i2;

            R2U2_DEBUG_PRINT("\tBZ ISQRT\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = sqrt %d (sqrt b%d)\n", inst_buff.addr,
                i2, i1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_FSQRT:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = sqrt(f1);

            (*monitor->value_buffer)[inst_buff.addr].f = f2;

            R2U2_DEBUG_PRINT("\tBZ FSQRT\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = sqrt%f (sqrt b%d)\n", inst_buff.addr,
                f2, f1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_IABS:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            i2 = (i1 < 0) ? (-1 * i1) : i1;

            (*monitor->value_buffer)[inst_buff.addr].i = i2;

            R2U2_DEBUG_PRINT("\tBZ IABS\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = abs %d (abs b%d)\n", inst_buff.addr,
                i2, i1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_FABS:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            f2 = (f1 < 0.0) ? (-1.0 * f1) : f1;

            (*monitor->value_buffer)[inst_buff.addr].f = f2;

            R2U2_DEBUG_PRINT("\tBZ FABS\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = abs %f (abs b%d)\n", inst_buff.addr,
                f2, f1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_IPREV:
            i1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].i;
            (*monitor->value_buffer)[inst_buff.addr].i = i1;

            R2U2_DEBUG_PRINT("\tBZ IPREV\n");
            R2U2_DEBUG_PRINT("\tb%d = %d (s%d)\n", inst_buff.addr, i1, inst_buff.param1.bz_addr);
            break;
        case R2U2_BZ_OP_FPREV:
            f1 = (*monitor->value_buffer)[inst_buff.param1.bz_addr].f;
            (*monitor->value_buffer)[inst_buff.addr].f = f1;

            R2U2_DEBUG_PRINT("\tBZ FPREV\n");
            R2U2_DEBUG_PRINT("\tb%d = %lf (s%d)\n", inst_buff.addr, f1, inst_buff.param1.bz_addr);
            break;
        default:
            R2U2_DEBUG_PRINT("Warning: Bad OpCode\n");
            break;
    }

    if(inst_buff.store) {
        (*(monitor->atomic_buffer)[0])[inst_buff.at_addr] = (*monitor->value_buffer)[inst_buff.addr].b;

        R2U2_DEBUG_PRINT("\tAT STORE\n");
        R2U2_DEBUG_PRINT("\ta%d = %hhu (b%d)\n", inst_buff.at_addr, (*(monitor->atomic_buffer)[0])[inst_buff.at_addr], inst_buff.addr);
    }

    return R2U2_OK;
}
