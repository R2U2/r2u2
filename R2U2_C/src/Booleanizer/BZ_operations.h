#ifndef BZ_OPERATIONS_H
#define BZ_OPERATIONS_H

void bz_store(bz_stack_t *, uint32_t);
void bz_ieq(bz_stack_t *);
void bz_feq(bz_stack_t *, float);
void bz_ineq(bz_stack_t *);
void bz_fneq(bz_stack_t *);
void bz_igt(bz_stack_t *);
void bz_fgt(bz_stack_t *);
void bz_igte(bz_stack_t *);
void bz_fgte(bz_stack_t *);
void bz_ilt(bz_stack_t *);
void bz_flt(bz_stack_t *);
void bz_ilte(bz_stack_t *);
void bz_flte(bz_stack_t *);
void bz_iadd(bz_stack_t *);
void bz_fadd(bz_stack_t *);
void bz_isub(bz_stack_t *);
void bz_fsub(bz_stack_t *);

#endif