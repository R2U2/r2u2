#ifndef BZ_OPERATIONS_H
#define BZ_OPERATIONS_H

#include "BZ_booleanizer.h"

/* Store, Load */
void bz_store(bz_booleanizer_t *, bz_val_t);
void bz_iload(bz_booleanizer_t *, bz_val_t);
void bz_fload(bz_booleanizer_t *, bz_val_t);

/* Ternary */
void bz_iite(bz_booleanizer_t *, bz_val_t);
void bz_fite(bz_booleanizer_t *, bz_val_t);

/* Bitwise */
void bz_bwneg(bz_booleanizer_t *, bz_val_t);
void bz_bwand(bz_booleanizer_t *, bz_val_t);
void bz_bwor(bz_booleanizer_t *, bz_val_t);
void bz_bwxor(bz_booleanizer_t *, bz_val_t);

/* Equality */
void bz_ieq(bz_booleanizer_t *, bz_val_t);
void bz_feq(bz_booleanizer_t *, bz_val_t);
void bz_ineq(bz_booleanizer_t *, bz_val_t);
void bz_fneq(bz_booleanizer_t *, bz_val_t);

/* Inequality  */
void bz_igt(bz_booleanizer_t *, bz_val_t);
void bz_fgt(bz_booleanizer_t *, bz_val_t);
void bz_igte(bz_booleanizer_t *, bz_val_t);
void bz_fgte(bz_booleanizer_t *, bz_val_t);
void bz_ilt(bz_booleanizer_t *, bz_val_t);
void bz_flt(bz_booleanizer_t *, bz_val_t);
void bz_ilte(bz_booleanizer_t *, bz_val_t);
void bz_flte(bz_booleanizer_t *, bz_val_t);

/* Arithmetic */
void bz_ineg(bz_booleanizer_t *, bz_val_t);
void bz_fneg(bz_booleanizer_t *, bz_val_t);
void bz_iadd(bz_booleanizer_t *, bz_val_t);
void bz_fadd(bz_booleanizer_t *, bz_val_t);
void bz_isub(bz_booleanizer_t *, bz_val_t);
void bz_fsub(bz_booleanizer_t *, bz_val_t);
void bz_imul(bz_booleanizer_t *, bz_val_t);
void bz_fmul(bz_booleanizer_t *, bz_val_t);
void bz_idiv(bz_booleanizer_t *, bz_val_t);
void bz_fdiv(bz_booleanizer_t *, bz_val_t);

/* Decoding function table */
extern void (*bz_decode[])(bz_booleanizer_t *, bz_val_t);

#endif