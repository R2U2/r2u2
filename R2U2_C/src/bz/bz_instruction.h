#ifndef BZ_INSTRUCTION_H
#define BZ_INSTRUCTION_H

#include <stdbool.h>

typedef enum bz_opcode {
    NONE    = 0b000000,
    /* Load/Store */
    STORE   = 0b000001,
    ILOAD   = 0b000010,
    FLOAD   = 0b000011,
    ICONST  = 0b000100,
    FCONST  = 0b000101,
    /* If-then-else */
    IITE    = 0b000110,
    FITE    = 0b000111,
    /* Bitwise */
    BWNEG   = 0b001000,
    BWAND   = 0b001001,
    BWOR    = 0b001010,
    BWXOR   = 0b001011,
    /* Equality */
    IEQ     = 0b001100,
    FEQ     = 0b001101,
    INEQ    = 0b001110,
    FNEQ    = 0b001111,
    /* Inequality */
    IGT     = 0b010000,
    FGT     = 0b010001,
    IGTE    = 0b010010,
    FGTE    = 0b010011,
    ILT     = 0b010100,
    FLT     = 0b010101,
    ILTE    = 0b010110,
    FLTE    = 0b010111,
    /* Arithmetic */
    INEG    = 0b011000,
    FNEG    = 0b011001,
    IADD    = 0b011010,
    FADD    = 0b011011,
    ISUB    = 0b011100,
    FSUB    = 0b011101,
    IMUL    = 0b011110,
    FMUL    = 0b011111,
    IDIV    = 0b100000,
    FDIV    = 0b100001,
    MOD     = 0b100010,
    /* Auxiliary */
    AUX1    = 0b100011,
    AUX2    = 0b100100,
    AUX3    = 0b100101,
    AUX4    = 0b100110,
} bz_opcode_t;

typedef struct bz_instruction {
    bz_opcode_t opcode;
    bz_val_t param;
} bz_instruction_t;

#endif