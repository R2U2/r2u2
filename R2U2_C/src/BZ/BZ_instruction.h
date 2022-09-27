#ifndef BZ_INSTRUCTION_H
#define BZ_INSTRUCTION_H

typedef enum bz_opcode {
    NONE    = 0b000000,
    /* Load/Store */
    STORE   = 0b000001,
    ILOAD   = 0b000010,
    FLOAD   = 0b000011,
    IITE    = 0b000100,
    FITE    = 0b000101,
    /* Bitwise */
    BWNEG   = 0b000110,
    BWAND   = 0b000111,
    BWOR    = 0b001000,
    BWXOR   = 0b001001,
    /* Equality */
    IEQ     = 0b001010,
    FEQ     = 0b001011,
    INEQ    = 0b001100,
    FNEQ    = 0b001101,
    /* Inequality */
    IGT     = 0b001110,
    FGT     = 0b001111,
    IGTE    = 0b010000,
    FGTE    = 0b010001,
    ILT     = 0b010010,
    FLT     = 0b010011,
    ILTE    = 0b010100,
    FLTE    = 0b010101,
    /* Arithmetic */
    INEG    = 0b010110,
    FNEG    = 0b010111,
    IADD    = 0b011000,
    FADD    = 0b011001,
    ISUB    = 0b011010,
    FSUB    = 0b011011,
    IMUL    = 0b011100,
    FMUL    = 0b011101,
    IDIV    = 0b011110,
    FDIV    = 0b011111,
    /* Auxiliary */
    AUX1    = 0b100000,
    AUX2    = 0b100001,
    AUX3    = 0b100010,
    AUX4    = 0b100011,
} bz_opcode_t;

typedef struct bz_instruction {
    bz_opcode_t opcode;
    bz_val_t param;
} bz_instruction_t;

#endif