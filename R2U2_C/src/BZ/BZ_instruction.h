#ifndef BZ_INSTRUCTION_H
#define BZ_INSTRUCTION_H

typedef enum bz_opcode {
    NONE,
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
    INEG,
    FNEG,
    /* Arithmetic  */
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
    AUX4
} bz_opcode_t;

typedef struct bz_instruction {
    bz_opcode_t opcode;
    uint32_t param;
} bz_instruction_t;

#endif