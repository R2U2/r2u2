#ifndef BZ_INSTRUCTION_H
#define BZ_INSTRUCTION_H

typedef enum bz_opcode {
    /* Load/Store */
    STORE,
    ILOAD,
    FLOAD,
    IITE,
    FITE,
    /* Bitwise */
    BWNEG,
    BWAND,
    BWOR,
    BWXOR,
    /* Equality */
    IEQ,
    FEQ,
    INEQ,
    FNEQ,
    /* Inequality */
    IGT,
    FGT,
    IGTE,
    FGTE,
    ILT,
    FLT,
    ILTE,
    FLTE,
    /* Arithmetic */
    INEG,
    FNEG,
    IADD,
    FADD,
    ISUB,
    FSUB,
    IMUL,
    FMUL,
    IDIV,
    FDIV,
    /* Auxiliary */
    AUX1,
    AUX2,
    AUX3,
    AUX4,
    NONE
} bz_opcode_t;

typedef struct bz_instruction {
    bz_opcode_t opcode;
    bz_val_t param;
} bz_instruction_t;

#endif