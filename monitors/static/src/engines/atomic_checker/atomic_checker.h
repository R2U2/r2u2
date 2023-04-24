#ifndef R2U2_ENGINES_AT_H
#define R2U2_ENGINES_AT_H

#include "r2u2.h"
#include "internals/errors.h"

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
    R2U2_AT_OP_FLOAT         = 0b0011,
    #if R2U2_AT_Extra_Filters
    R2U2_AT_OP_RATE           = 0b0100,
    R2U2_AT_OP_ABS_DIFF_ANGLE = 0b0101,
    R2U2_AT_OP_MOVAVG         = 0b0110,
    #endif
    #if R2U2_AT_Signal_Sets
    R2U2_AT_OP_EXACTLY_ONE_OF = 0b0111, // NOTE: sig_addr stores set_addr
    R2U2_AT_OP_NONE_OF        = 0b1000,
    R2U2_AT_OP_ALL_OF         = 0b1001
    #endif
} r2u2_at_filter_t;

typedef union {
    // TODO(bckempa): Pun these to types.h
    int8_t s;
    r2u2_bool b;
    int32_t i;
    r2u2_float d;
} r2u2_at_comparison_arg_t;

typedef union {
    r2u2_float epsilon;     /* epsilon value for float comparsions */
    #if R2U2_AT_Extra_Filters
    r2u2_float diff_angle;  /* abs_diff_angle filter */
    r2u2_float prev;                /* rate filter */
    // TODO(bckempa): the movAvg type is waaaaaay bigger than anything else....
    movAvg_t *movavg;       /* movavg filter */
    #endif
} r2u2_at_filter_aux_data_t;

typedef struct {
    r2u2_at_conditional_t conditional;
    r2u2_at_filter_t filter;
    uint8_t sig_addr;
    uint8_t atom_addr;
    bool comp_is_sig;
    r2u2_at_comparison_arg_t comparison;
    r2u2_at_filter_aux_data_t filt_data_struct;
} r2u2_at_instruction_t;

r2u2_status_t r2u2_at_instruction_dispatch(r2u2_monitor_t*, r2u2_at_instruction_t *);

#endif /* R2U2_ENGINES_AT_H */