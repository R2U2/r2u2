#ifndef BZ_OPERATIONS_H
#define BZ_OPERATIONS_H

/* Store, Load */
void bz_store(bz_stack_t *, bz_val_t);
void bz_load(bz_stack_t *, bz_val_t);

/* Ternary */
void bz_iite(bz_stack_t *, bz_val_t);
void bz_fite(bz_stack_t *, bz_val_t);

/* Bitwise */
void bz_bwneg(bz_stack_t *, bz_val_t);
void bz_bwand(bz_stack_t *, bz_val_t);
void bz_bwor(bz_stack_t *, bz_val_t);
void bz_bwxor(bz_stack_t *, bz_val_t);

/* Equality */
void bz_ieq(bz_stack_t *, bz_val_t);
void bz_feq(bz_stack_t *, bz_val_t);
void bz_ineq(bz_stack_t *, bz_val_t);
void bz_fneq(bz_stack_t *, bz_val_t);

/* Inequality  */
void bz_igt(bz_stack_t *, bz_val_t);
void bz_fgt(bz_stack_t *, bz_val_t);
void bz_igte(bz_stack_t *, bz_val_t);
void bz_fgte(bz_stack_t *, bz_val_t);
void bz_ilt(bz_stack_t *, bz_val_t);
void bz_flt(bz_stack_t *, bz_val_t);
void bz_ilte(bz_stack_t *, bz_val_t);
void bz_flte(bz_stack_t *, bz_val_t);

/* Arithmetic */
void bz_ineg(bz_stack_t *, bz_val_t);
void bz_fneg(bz_stack_t *, bz_val_t);
void bz_iadd(bz_stack_t *, bz_val_t);
void bz_fadd(bz_stack_t *, bz_val_t);
void bz_isub(bz_stack_t *, bz_val_t);
void bz_fsub(bz_stack_t *, bz_val_t);
void bz_imul(bz_stack_t *, bz_val_t);
void bz_fmul(bz_stack_t *, bz_val_t);
void bz_idiv(bz_stack_t *, bz_val_t);
void bz_fdiv(bz_stack_t *, bz_val_t);

#endif