#include "BZ_operations.h"

void bz_store(bz_stack_t *stack, uint32_t addr)
{
    bool val;
    val = bz_stack_pop(stack)->b;
    atomics_vector[addr] = val;
}

void bz_ieq(bz_stack_t *stack)
{
    uint32_t i1, i2;
    bool res;

    i1 = bz_stack_pop(stack)->i;
    i2 = bz_stack_pop(stack)->i;
    res = i1 == i2;

    bz_stack_bpush(stack,res);
}

void bz_feq(bz_stack_t *stack, float epsilon)
{
    float f1, f2;
    bool res;

    i1 = bz_stack_pop(stack)->i;
    i2 = bz_stack_pop(stack)->i;
    res = (i1 - i2 <= epsilon) || (i2 - i1 <= epsilon);

    bz_stack_bpush(stack,res);
}

void bz_ineq(bz_stack_t *stack)
{
    uint32_t i1, i2;
    bool res;

    i1 = bz_stack_pop(stack)->i;
    i2 = bz_stack_pop(stack)->i;
    res = i1 != i2;

    bz_stack_bpush(stack,res);
}

void bz_fneq(bz_stack_t *stack);
void bz_igt(bz_stack_t *stack);
void bz_fgt(bz_stack_t *stack);
void bz_igte(bz_stack_t *stack);
void bz_fgte(bz_stack_t *stack);
void bz_ilt(bz_stack_t *stack);
void bz_flt(bz_stack_t *stack);

void bz_iadd(bz_stack_t *stack)
{
    uint32_t i1, i2, res;

    i1 = bz_stack_pop(stack)->i;
    i2 = bz_stack_pop(stack)->i;
    res = i1 + i2;

    bz_stack_ipush(stack,res);
}

void bz_fadd(bz_stack_t *)
{
    float f1, f2, res;

    f1 = bz_stack_pop(stack)->f;
    f2 = bz_stack_pop(stack)->f;
    res = f1 + f2;

    bz_stack_fpush(stack,res);
}

void bz_isub(bz_stack_t *)
{
    uint32_t i1, i2, res;

    i1 = bz_stack_pop(stack)->i;
    i2 = bz_stack_pop(stack)->i;
    res = i1 - i2;

    bz_stack_ipush(stack,res);
}

void bz_fsub(bz_stack_t *)
{
    float f1, f2, res;

    f1 = bz_stack_pop(stack)->f;
    f2 = bz_stack_pop(stack)->f;
    res = f1 + f2;

    bz_stack_fpush(stack,res);
}