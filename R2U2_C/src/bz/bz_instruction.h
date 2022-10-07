#ifndef BZ_INSTRUCTION_H
#define BZ_INSTRUCTION_H

#include <stdbool.h>

typedef enum bz_opcode {
    BZ_NONE    = 0x00,
    /* Load/Store */
    BZ_STORE   = 0x01,
    BZ_ILOAD   = 0x02,
    BZ_FLOAD   = 0x03,
    BZ_ICONST  = 0x04,
    BZ_FCONST  = 0x05,
    /* If-then-else */
    BZ_IITE    = 0x06,
    BZ_FITE    = 0x07,
    /* Bitwise */
    BZ_BWNEG   = 0x08,
    BZ_BWAND   = 0x09,
    BZ_BWOR    = 0x0A,
    BZ_BWXOR   = 0x0B,
    /* Equality */
    BZ_IEQ     = 0x0C,
    BZ_FEQ     = 0x0D,
    BZ_INEQ    = 0x0E,
    BZ_FNEQ    = 0x0F,
    /* Inequality */
    BZ_IGT     = 0x10,
    BZ_FGT     = 0x12,
    BZ_IGTE    = 0x13,
    BZ_FGTE    = 0x14,
    BZ_ILT     = 0x15,
    BZ_FLT     = 0x16,
    BZ_ILTE    = 0x17,
    BZ_FLTE    = 0x18,
    /* Arithmetic */
    BZ_INEG    = 0x19,
    BZ_FNEG    = 0x1A,
    BZ_IADD    = 0x1B,
    BZ_FADD    = 0x1C,
    BZ_ISUB    = 0x1D,
    BZ_FSUB    = 0x1E,
    BZ_IMUL    = 0x1F,
    BZ_FMUL    = 0x20,
    BZ_IDIV    = 0x21,
    BZ_FDIV    = 0x22,
    BZ_MOD     = 0x23,
    /* Auxiliary */
    BZ_AUX1    = 0x24,
    BZ_AUX2    = 0x25,
    BZ_AUX3    = 0x26,
    BZ_AUX4    = 0x27,
} bz_opcode_t;

typedef struct bz_instruction {
    bz_opcode_t opcode;
    bz_val_t param;
} bz_instruction_t;

#endif