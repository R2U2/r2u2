#ifndef BZ_BOOLEANIZER_H
#define BZ_BOOLEANIZER_H

#include <stdint.h>
#include <stdbool.h>

#include "r2u2.h"
#include "internals/types.h"

typedef enum r2u2_bz_opcode {
    R2U2_BZ_OP_NONE    = 0b000000,
    /* Loads */
    R2U2_BZ_OP_ILOAD   = 0b000001,
    R2U2_BZ_OP_FLOAD   = 0b000010,
    R2U2_BZ_OP_ICONST  = 0b000011,
    R2U2_BZ_OP_FCONST  = 0b000100,
     /* Store */
    R2U2_BZ_OP_STORE   = 0b000101,
    /* Bitwise */
    R2U2_BZ_OP_BWNEG   = 0b000110,
    R2U2_BZ_OP_BWAND   = 0b000111,
    R2U2_BZ_OP_BWOR    = 0b001000,
    R2U2_BZ_OP_BWXOR   = 0b001001,
    /* Equality */
    R2U2_BZ_OP_IEQ     = 0b001010,
    R2U2_BZ_OP_FEQ     = 0b001011,
    R2U2_BZ_OP_INEQ    = 0b001100,
    R2U2_BZ_OP_FNEQ    = 0b001101,
    /* Inequality */
    R2U2_BZ_OP_IGT     = 0b001110,
    R2U2_BZ_OP_FGT     = 0b001111,
    R2U2_BZ_OP_IGTE    = 0b010000,
    R2U2_BZ_OP_FGTE    = 0b010001,
    R2U2_BZ_OP_ILT     = 0b010010,
    R2U2_BZ_OP_FLT     = 0b010011,
    R2U2_BZ_OP_ILTE    = 0b010100,
    R2U2_BZ_OP_FLTE    = 0b010101,
    /* Arithmetic */
    R2U2_BZ_OP_INEG    = 0b010110,
    R2U2_BZ_OP_FNEG    = 0b010111,
    R2U2_BZ_OP_IADD    = 0b011000,
    R2U2_BZ_OP_FADD    = 0b011001,
    R2U2_BZ_OP_ISUB    = 0b011010,
    R2U2_BZ_OP_FSUB    = 0b011011,
    R2U2_BZ_OP_IMUL    = 0b011100,
    R2U2_BZ_OP_FMUL    = 0b011101,
    R2U2_BZ_OP_IDIV    = 0b011110,
    R2U2_BZ_OP_FDIV    = 0b011111,
    R2U2_BZ_OP_MOD     = 0b100000,
    R2U2_BZ_OP_IPOW    = 0b100001,
    R2U2_BZ_OP_FPOW    = 0b100010,
    R2U2_BZ_OP_ISQRT   = 0b100011,
    R2U2_BZ_OP_FSQRT   = 0b100100,
    R2U2_BZ_OP_IABS    = 0b100101,
    R2U2_BZ_OP_FABS    = 0b100110,
    R2U2_BZ_OP_PREV    = 0b100111,
    R2U2_BZ_TS         = 0b101000,
} r2u2_bz_opcode_t;

// Booleanizer parameters are one of:
// (1) an address in Booleanizer memory
// (2) a constant int
// (3) a constant float
typedef union r2u2_bz_param {
    uint32_t bz_addr;
    r2u2_int bz_int;
    r2u2_float bz_float;
} r2u2_bz_param_t;

typedef struct r2u2_bz_instruction {
    r2u2_bz_param_t param1;
    uint32_t param2;
    uint32_t memory_reference;
    uint8_t opcode;
} r2u2_bz_instruction_t;


r2u2_status_t r2u2_bz_instruction_dispatch(r2u2_monitor_t *, r2u2_bz_instruction_t *);

#endif
