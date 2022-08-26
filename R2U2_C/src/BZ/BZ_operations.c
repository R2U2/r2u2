#include <stdio.h>

#include "BZ_operations.h"

void bz_store(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t addr;
    bool val;

    addr = param.i;

    val = bz_stack_pop(&bz->stack).b;
    printf("%hhu\n",val);
}

void bz_iload(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t addr, val;

    addr = param.i;

    val = bz->sig_vector[addr].i;

    bz_stack_ipush(&bz->stack,val);
}

void bz_fload(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t addr;
    float val;

    addr = param.i;

    val = bz->sig_vector[addr].f;

    bz_stack_fpush(&bz->stack,val);
}

void bz_iite(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_fite(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_bwneg(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_bwand(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_bwor(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_bwxor(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_ieq(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t i1, i2;
    bool res;

    i1 = bz_stack_pop(&bz->stack).i;
    i2 = bz_stack_pop(&bz->stack).i;
    res = i1 == i2;

    printf("%d,%d,%hhu\n",i1,i2,res);

    bz_stack_bpush(&bz->stack,res);
}

void bz_feq(bz_booleanizer_t *bz, bz_val_t param)
{
    float f1, f2, epsilon;
    bool res;

    epsilon = param.f;

    f1 = bz_stack_pop(&bz->stack).f;
    f2 = bz_stack_pop(&bz->stack).f;
    res = (f1 - f2 <= epsilon) || (f2 - f1 <= epsilon);

    bz_stack_bpush(&bz->stack,res);
}

void bz_ineq(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t i1, i2;
    bool res;

    i1 = bz_stack_pop(&bz->stack).i;
    i2 = bz_stack_pop(&bz->stack).i;
    res = i1 != i2;

    bz_stack_bpush(&bz->stack,res);
}

void bz_fneq(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_igt(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_fgt(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_igte(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_fgte(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_ilt(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_flt(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_ilte(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_flte(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_ineg(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_fneg(bz_booleanizer_t *bz, bz_val_t param)
{
    return;
}

void bz_iadd(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t i1, i2, res;

    i1 = bz_stack_pop(&bz->stack).i;
    i2 = bz_stack_pop(&bz->stack).i;
    res = i1 + i2;

    bz_stack_ipush(&bz->stack,res);
}

void bz_fadd(bz_booleanizer_t *bz, bz_val_t param)
{
    float f1, f2, res;

    f1 = bz_stack_pop(&bz->stack).f;
    f2 = bz_stack_pop(&bz->stack).f;
    res = f1 + f2;

    bz_stack_fpush(&bz->stack,res);
}

void bz_isub(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t i1, i2, res;

    i1 = bz_stack_pop(&bz->stack).i;
    i2 = bz_stack_pop(&bz->stack).i;
    res = i1 - i2;

    bz_stack_ipush(&bz->stack,res);
}

void bz_fsub(bz_booleanizer_t *bz, bz_val_t param)
{
    float f1, f2, res;

    f1 = bz_stack_pop(&bz->stack).f;
    f2 = bz_stack_pop(&bz->stack).f;
    res = f1 + f2;

    bz_stack_fpush(&bz->stack,res);
}

void bz_imul(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t i1, i2, res;

    i1 = bz_stack_pop(&bz->stack).i;
    i2 = bz_stack_pop(&bz->stack).i;
    res = i1 * i2;

    bz_stack_ipush(&bz->stack,res);
}

void bz_fmul(bz_booleanizer_t *bz, bz_val_t param)
{
    float f1, f2, res;

    f1 = bz_stack_pop(&bz->stack).f;
    f2 = bz_stack_pop(&bz->stack).f;
    res = f1 * f2;

    bz_stack_fpush(&bz->stack,res);
}

void bz_idiv(bz_booleanizer_t *bz, bz_val_t param)
{
    uint32_t i1, i2, res;

    i1 = bz_stack_pop(&bz->stack).i;
    i2 = bz_stack_pop(&bz->stack).i;
    res = i1 / i2;

    bz_stack_ipush(&bz->stack,res);
}

void bz_fdiv(bz_booleanizer_t *bz, bz_val_t param)
{
    float f1, f2, res;

    f1 = bz_stack_pop(&bz->stack).f;
    f2 = bz_stack_pop(&bz->stack).f;
    res = f1 / f2;

    bz_stack_fpush(&bz->stack,res);
}

void (*bz_decode[])(bz_booleanizer_t *, bz_val_t) = {
    bz_store,
    bz_iload,
    bz_fload,
    bz_iite,
    bz_fite,
    bz_bwneg,
    bz_bwand,
    bz_bwor,
    bz_bwxor,
    bz_ieq,
    bz_feq,
    bz_ineq,
    bz_fneq,
    bz_igt,
    bz_fgt,
    bz_igte,
    bz_fgte,
    bz_ilt,
    bz_flt,
    bz_ilte,
    bz_flte,
    bz_ineg,
    bz_fneg,
    bz_iadd,
    bz_fadd,
    bz_isub,
    bz_fsub,
    bz_imul,
    bz_fmul,
    bz_idiv,
    bz_fdiv
};