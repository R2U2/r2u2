#ifndef R2U2_ENGINES_MLTL_H
#define R2U2_ENGINES_MLTL_H

#include "r2u2.h"

#define R2U2_MLTL_TENSE_FUTURE 0b10000

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

typedef uint8_t r2u2_mltl_opcode_t;

enum r2u2_mltl_operand_type{
    R2U2_FT_OP_DIRECT      = 0b01,
    R2U2_FT_OP_ATOMIC      = 0b00,
    R2U2_FT_OP_SUBFORMULA  = 0b10,
    R2U2_FT_OP_NOT_SET     = 0b11
};

typedef uint8_t r2u2_mltl_operand_type_t;

//
// data structure for instruction
// not packed
// instruction format for packed representation:
//
typedef struct {
  uint32_t                   op1_value;
  uint32_t                   op2_value;
  uint32_t                   memory_reference;
  r2u2_mltl_operand_type_t   op1_type;
  r2u2_mltl_operand_type_t   op2_type;
  r2u2_mltl_opcode_t         opcode;
} r2u2_mltl_instruction_t;

r2u2_status_t r2u2_mltl_instruction_dispatch(r2u2_monitor_t *, r2u2_mltl_instruction_t *);

#endif /* R2U2_ENGINES_MLTL_H */
