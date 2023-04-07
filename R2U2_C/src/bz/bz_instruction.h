#ifndef BZ_INSTRUCTION_H
#define BZ_INSTRUCTION_H

#include <stdbool.h>

typedef uint8_t bz_int_t;
typedef float bz_float_t;

typedef union bz_val {
    bool b;
    bz_int_t i;
    bz_float_t f;
} bz_val_t;

typedef enum bz_opcode {
    BZ_NONE    = 0b000000,
    /* Loads */
    BZ_ILOAD   = 0b000010,
    BZ_FLOAD   = 0b000011,
    BZ_ICONST  = 0b000100,
    BZ_FCONST  = 0b000101,
    /* If-then-else */
    BZ_IITE    = 0b000110,
    BZ_FITE    = 0b000111,
    /* Bitwise */
    BZ_BWNEG   = 0b001000,
    BZ_BWAND   = 0b001001,
    BZ_BWOR    = 0b001010,
    BZ_BWXOR   = 0b001011,
    /* Equality */
    BZ_IEQ     = 0b001100,
    BZ_FEQ     = 0b001101,
    BZ_INEQ    = 0b001110,
    BZ_FNEQ    = 0b001111,
    /* Inequality */
    BZ_IGT     = 0b010000,
    BZ_FGT     = 0b010001,
    BZ_IGTE    = 0b010010,
    BZ_FGTE    = 0b010011,
    BZ_ILT     = 0b010100,
    BZ_FLT     = 0b010101,
    BZ_ILTE    = 0b010110,
    BZ_FLTE    = 0b010111,
    /* Arithmetic */
    BZ_INEG    = 0b011000,
    BZ_FNEG    = 0b011001,
    BZ_IADD    = 0b011010,
    BZ_FADD    = 0b011011,
    BZ_ISUB    = 0b011100,
    BZ_FSUB    = 0b011101,
    BZ_IMUL    = 0b011110,
    BZ_FMUL    = 0b011111,
    BZ_IDIV    = 0b100000,
    BZ_FDIV    = 0b100001,
    BZ_MOD     = 0b100010,
    /* Auxiliary */
    BZ_AUX1    = 0b100011,
    BZ_AUX2    = 0b100100,
    BZ_AUX3    = 0b100101,
    BZ_AUX4    = 0b100110,
} bz_opcode_t;

typedef struct bz_instruction {
    bz_opcode_t opcode;
    bz_val_t param;
} bz_instruction_t;

#endif