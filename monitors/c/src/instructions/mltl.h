#ifndef MLTL_INSTRUCTIONS_H
#define MLTL_INSTRUCTIONS_H
#include <stdint.h>

enum r2u2_mltl_opcode{
    // Future Tense: 1xxxx

    R2U2_MLTL_OP_NOP          = 0b11111,
    R2U2_MLTL_OP_CONFIGURE    = 0b11110,
    R2U2_MLTL_OP_LOAD         = 0b11101,
    R2U2_MLTL_OP_RETURN       = 0b11100,

    R2U2_MLTL_OP_EVENTUALLY   = 0b11011,
    R2U2_MLTL_OP_GLOBALLY     = 0b11010,
    R2U2_MLTL_OP_UNTIL        = 0b11001,
    R2U2_MLTL_OP_RELEASE      = 0b11000,

    R2U2_MLTL_OP_NOT          = 0b10111,
    R2U2_MLTL_OP_AND          = 0b10110,
    R2U2_MLTL_OP_OR           = 0b10101,
    R2U2_MLTL_OP_IMPLIES      = 0b10100,

    R2U2_MLTL_OP_XOR          = 0b10001,
    R2U2_MLTL_OP_EQUIVALENT   = 0b10000,

    // Past Tense: 0xxxx

    R2U2_MLTL_OP_ONCE         = 0b01011,
    R2U2_MLTL_OP_HISTORICALLY = 0b01010,
    R2U2_MLTL_OP_SINCE        = 0b01001,
    R2U2_MLTL_OP_TRIGGER      = 0b01000,
};

enum r2u2_mltl_operand_type{
    R2U2_FT_OP_DIRECT      = 0b01,
    R2U2_FT_OP_ATOMIC      = 0b00,
    R2U2_FT_OP_SUBFORMULA  = 0b10,
    R2U2_FT_OP_NOT_SET     = 0b11
};

typedef struct {
  uint32_t    op1_value;
  uint32_t    op2_value;
  uint32_t    memory_reference;
  uint8_t     op1_type;
  uint8_t     op2_type;
  uint8_t     opcode;
} r2u2_mltl_instruction_t;

r2u2_mltl_instruction_t r2u2_mltl_set_from_binary(uint8_t *);

#endif
