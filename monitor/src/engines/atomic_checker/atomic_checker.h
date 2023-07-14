#ifndef R2U2_ENGINES_AT_H
#define R2U2_ENGINES_AT_H

#include "r2u2.h"
#include "internals/errors.h"

#if R2U2_AT_EXTRA_FILTERS
#include "extra_filters/filter_movavg.h"
#endif

typedef enum {
    R2U2_AT_COND_EQ  = 0b000,
    R2U2_AT_COND_NEQ = 0b001,
    R2U2_AT_COND_LT  = 0b010,
    R2U2_AT_COND_LEQ = 0b011,
    R2U2_AT_COND_GT  = 0b100,
    R2U2_AT_COND_GEQ = 0b101
} r2u2_at_conditional_t;

typedef enum {
    R2U2_AT_OP_BOOL           = 0b0001,
    R2U2_AT_OP_INT            = 0b0010,
    R2U2_AT_OP_FLOAT          = 0b0011,
    R2U2_AT_OP_FORMULA        = 0b0100,
    #if R2U2_AT_EXTRA_FILTERS
    R2U2_AT_OP_RATE           = 0b0101,
    R2U2_AT_OP_ABS_DIFF_ANGLE = 0b0110,
    R2U2_AT_OP_MOVAVG         = 0b0111,
    #endif
    #if R2U2_AT_Signal_Sets
    R2U2_AT_OP_EXACTLY_ONE_OF = 0b1000, // NOTE: sig_addr stores set_addr
    R2U2_AT_OP_NONE_OF        = 0b1001,
    R2U2_AT_OP_ALL_OF         = 0b1010
    #endif
} r2u2_at_filter_t;

typedef union {
    // TODO(bckempa): Pun these to types.h
    int8_t s;
    r2u2_bool b;
    r2u2_int i;
    r2u2_float d;
} r2u2_at_arg_t;

typedef struct {
    r2u2_at_conditional_t conditional;
    r2u2_at_filter_t filter;
    uint8_t sig_addr;
    uint8_t atom_addr;
    bool comp_is_sig;
    r2u2_at_arg_t comparison;
    r2u2_at_arg_t filter_arg;
    uint8_t aux_addr;
} r2u2_at_instruction_t;

r2u2_status_t r2u2_at_instruction_dispatch(r2u2_monitor_t*, r2u2_at_instruction_t *);

#endif /* R2U2_ENGINES_AT_H */
