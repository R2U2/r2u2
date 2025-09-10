#include <stdio.h>
#include <math.h>

#include "booleanizer.h"
#include "internals/debug.h"

r2u2_status_t r2u2_bz_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_bz_instruction_t *instr)
{
    r2u2_int i1, i2;
    r2u2_float f1, f2;

    switch(instr->opcode) {
        case R2U2_BZ_OP_NONE: 
            break;
        /* Load */
        case R2U2_BZ_OP_ILOAD:
            sscanf((monitor->signal_vector)[instr->param1], "%d", &i1);
            (monitor->value_buffer)[instr->memory_reference].i = i1;

            R2U2_DEBUG_PRINT("\tBZ ILOAD\n");
            R2U2_DEBUG_PRINT("\tb%d = %d (s%d)\n", instr->memory_reference, i1, instr->param1);
            break;
        case R2U2_BZ_OP_FLOAD:
            sscanf((monitor->signal_vector)[instr->param1], "%lf", &f1);
            (monitor->value_buffer)[instr->memory_reference].f = f1;

            R2U2_DEBUG_PRINT("\tBZ FLOAD\n");
            R2U2_DEBUG_PRINT("\tb%d = %lf (s%d)\n", instr->memory_reference, f1, instr->param1);
            break;
        /* Store */
        case R2U2_BZ_OP_STORE:
            (monitor->atomic_buffer)[instr->param2] = (monitor->value_buffer)[instr->param1].i;

            R2U2_DEBUG_PRINT("\ta%d = %hhu (b%d)\n", instr->param2, (monitor->atomic_buffer)[instr->param2], instr->param1);
            break;
        /* Bitwise */
        case R2U2_BZ_OP_BWNEG:
            i1 = (monitor->value_buffer)[instr->param1].i;
            (monitor->value_buffer)[instr->memory_reference].i = ~i1;

            R2U2_DEBUG_PRINT("\tBZ BW NEG\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = ~%d (~b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, instr->param1);
            break;
        case R2U2_BZ_OP_BWAND:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 & i2;

            R2U2_DEBUG_PRINT("\tBZ BW AND\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d & %d (b%d & b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_BWOR:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 | i2;

            R2U2_DEBUG_PRINT("\tBZ BW OR\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d | %d (b%d | b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_BWXOR:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 ^ i2;

            R2U2_DEBUG_PRINT("\tBZ BW XOR\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d ^ %d (b%d ^ b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        /* Equality */
        case R2U2_BZ_OP_IEQ:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 == i2;

            R2U2_DEBUG_PRINT("\tBZ IEQ\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d == %d (b%d == b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FEQ:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].i = (f1 > f2) ? (f1 - f2 < R2U2_FLOAT_EPSILON) : (f2 - f1 < R2U2_FLOAT_EPSILON);

            R2U2_DEBUG_PRINT("\tBZ FEQ\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f == %f +- %f (b%d == b%d +- %f)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, f1, f2, R2U2_FLOAT_EPSILON, instr->param1, instr->param2, R2U2_FLOAT_EPSILON);
            break;
        case R2U2_BZ_OP_INEQ:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 != i2;

            R2U2_DEBUG_PRINT("\tBZ INEQ\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d != %d (b%d != b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FNEQ:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].i = !((f1 > f2) ? (f1 - f2 < R2U2_FLOAT_EPSILON) : (f2 - f1 < R2U2_FLOAT_EPSILON));

            R2U2_DEBUG_PRINT("\tBZ FLT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f != %f +- %f (b%d != b%d +- %f)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, f1, f2, R2U2_FLOAT_EPSILON, instr->param1, instr->param2, R2U2_FLOAT_EPSILON);
            break;
        /* Inequality */
        case R2U2_BZ_OP_IGT:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 > i2;
            R2U2_DEBUG_PRINT("\tBZ IGT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d > %d (b%d > b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FGT:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].i = f1 > f2;

            R2U2_DEBUG_PRINT("\tBZ FGT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f > %f (b%d > b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, f1, f2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_IGTE:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 >= i2;

            R2U2_DEBUG_PRINT("\tBZ IGTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d >= %d (b%d >= b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FGTE:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].i = (f1 > f2 - R2U2_FLOAT_EPSILON);

            R2U2_DEBUG_PRINT("\tBZ FGTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f >= %f - %f (b%d == b%d - %f)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, f1, f2, R2U2_FLOAT_EPSILON, instr->param1, instr->param2, R2U2_FLOAT_EPSILON);
            break;
        case R2U2_BZ_OP_ILT:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 < i2;

            R2U2_DEBUG_PRINT("\tBZ ILT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d < %d (b%d < b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FLT:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].i = f1 < f2;

            R2U2_DEBUG_PRINT("\tBZ FLT\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f < %f (b%d < b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, f1, f2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_ILTE:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 <= i2;

            R2U2_DEBUG_PRINT("\tBZ ILTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %d <= %d (b%d <= b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FLTE:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].i = (f1 < f2 + R2U2_FLOAT_EPSILON);

            R2U2_DEBUG_PRINT("\tBZ FLTE\n");
            R2U2_DEBUG_PRINT("\tb%d = %hhu = %f <= %f + %f (b%d == b%d + %f)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, f1, f2, R2U2_FLOAT_EPSILON, instr->param1, instr->param2, R2U2_FLOAT_EPSILON);
            break;
        /* Arithmetic */
        case R2U2_BZ_OP_INEG:
            i1 = (monitor->value_buffer)[instr->param1].i;
            (monitor->value_buffer)[instr->memory_reference].i = -i1;

            R2U2_DEBUG_PRINT("\tBZ INEG\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = -%d (-b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, instr->param1);
            break;
        case R2U2_BZ_OP_FNEG:
            f1 = (monitor->value_buffer)[instr->param1].f;
            (monitor->value_buffer)[instr->memory_reference].f = -f1;

            R2U2_DEBUG_PRINT("\tBZ FNEG\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = -%f (-b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, instr->param1);
            break;
        case R2U2_BZ_OP_IADD:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 + i2;

            R2U2_DEBUG_PRINT("\tBZ IADD\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d + %d (b%d + b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FADD:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].f = f1 + f2;

            R2U2_DEBUG_PRINT("\tBZ FADD\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f + %f (b%d + b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, f2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_ISUB:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 - i2;

            R2U2_DEBUG_PRINT("\tBZ ISUB\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d - %d (b%d - b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FSUB:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].f = f1 - f2;

            R2U2_DEBUG_PRINT("\tBZ FSUB\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f - %f (b%d - b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, f2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_IMUL:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 * i2;

            R2U2_DEBUG_PRINT("\tBZ IMUL\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d * %d (b%d * b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FMUL:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].f = f1 * f2;

            R2U2_DEBUG_PRINT("\tBZ FMUL\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f * %f (b%d * b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, f2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_IDIV:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 / i2;

            R2U2_DEBUG_PRINT("\tBZ IDIV\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d / %d (b%d / b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FDIV:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].f = f1 / f2;

            R2U2_DEBUG_PRINT("\tBZ FDIV\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f / %f (b%d / b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, f2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_MOD:
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = i1 % i2;

            R2U2_DEBUG_PRINT("\tBZ IMOD\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d %% %d (b%d %% b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_IPOW: 
            i1 = (monitor->value_buffer)[instr->param1].i;
            i2 = (monitor->value_buffer)[instr->param2].i;
            (monitor->value_buffer)[instr->memory_reference].i = pow(i1,i2);

            R2U2_DEBUG_PRINT("\tBZ IPOW\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = %d pow %d (b%d pow b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, i2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_FPOW:
            f1 = (monitor->value_buffer)[instr->param1].f;
            f2 = (monitor->value_buffer)[instr->param2].f;
            (monitor->value_buffer)[instr->memory_reference].f = pow(f1,f2);

            R2U2_DEBUG_PRINT("\tBZ FPOW\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = %f pow %f (b%d pow b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, f2, instr->param1, instr->param2);
            break;
        case R2U2_BZ_OP_ISQRT:
            i1 = (monitor->value_buffer)[instr->param1].i;
            (monitor->value_buffer)[instr->memory_reference].i = sqrt(i1);

            R2U2_DEBUG_PRINT("\tBZ ISQRT\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = sqrt %d (sqrt b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, instr->param1);
            break;
        case R2U2_BZ_OP_FSQRT:
            f1 = (monitor->value_buffer)[instr->param1].f;
            (monitor->value_buffer)[instr->memory_reference].f = sqrt(f1);

            R2U2_DEBUG_PRINT("\tBZ FSQRT\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = sqrt %f (sqrt b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, instr->param1);
            break;
        case R2U2_BZ_OP_IABS:
            i1 = (monitor->value_buffer)[instr->param1].i;
            (monitor->value_buffer)[instr->memory_reference].i = (i1 < 0) ? (-1 * i1) : i1;

            R2U2_DEBUG_PRINT("\tBZ IABS\n");
            R2U2_DEBUG_PRINT("\tb%d = %d = abs %d (abs b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].i, i1, instr->param1);
            break;
        case R2U2_BZ_OP_FABS:
            f1 = (monitor->value_buffer)[instr->param1].f;
            (monitor->value_buffer)[instr->memory_reference].f = (f1 < 0.0) ? (-1.0 * f1) : f1;

            R2U2_DEBUG_PRINT("\tBZ FABS\n");
            R2U2_DEBUG_PRINT("\tb%d = %f = abs %f (abs b%d)\n", instr->memory_reference,
                (monitor->value_buffer)[instr->memory_reference].f, f1, instr->param1);
            break;
        case R2U2_BZ_OP_PREV:
            (monitor->value_buffer)[instr->memory_reference] = (monitor->value_buffer)[instr->param1];

            R2U2_DEBUG_PRINT("\tBZ PREV\n");
            R2U2_DEBUG_PRINT("\tb%d = (s%d)\n", instr->memory_reference, instr->param1);
            break;
        case R2U2_BZ_TS:
            (monitor->value_buffer)[instr->memory_reference].i = (monitor->time_stamp > (INT32_MAX)) ? INT32_MAX : monitor->time_stamp;

            R2U2_DEBUG_PRINT("\tBZ TS\n");
            R2U2_DEBUG_PRINT("\tb%d = %d\n", instr->memory_reference, monitor->time_stamp);
            break;
        default:
            R2U2_DEBUG_PRINT("Warning: Bad OpCode\n");
            break;
    }

    return R2U2_OK;
}
