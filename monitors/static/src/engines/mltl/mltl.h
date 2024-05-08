#ifndef R2U2_ENGINES_MLTL_H
#define R2U2_ENGINES_MLTL_H

#include "r2u2.h"

#define R2U2_MLTL_TENSE_FUTURE 0b10000

typedef enum {
    // Future Tense: 1xxxx

    R2U2_MLTL_OP_FT_NOP          = 0b11111,
    R2U2_MLTL_OP_FT_CONFIGURE    = 0b11110,
    R2U2_MLTL_OP_FT_LOAD         = 0b11101,
    R2U2_MLTL_OP_FT_RETURN       = 0b11100,

    R2U2_MLTL_OP_FT_EVENTUALLY   = 0b11011,
    R2U2_MLTL_OP_FT_GLOBALLY     = 0b11010,
    R2U2_MLTL_OP_FT_UNTIL        = 0b11001,
    R2U2_MLTL_OP_FT_RELEASE      = 0b11000,

    R2U2_MLTL_OP_FT_NOT          = 0b10111,
    R2U2_MLTL_OP_FT_AND          = 0b10110,
    R2U2_MLTL_OP_FT_OR           = 0b10101,
    R2U2_MLTL_OP_FT_IMPLIES      = 0b10100,

    R2U2_MLTL_OP_FT_PROB         = 0b10011,
    R2U2_MLTL_OP_FT_NOR          = 0b10010,
    R2U2_MLTL_OP_FT_XOR          = 0b10001,
    R2U2_MLTL_OP_FT_EQUIVALENT   = 0b10000,


    // Past Tense: 0xxxx

    R2U2_MLTL_OP_PT_NOP          = 0b01111,
    R2U2_MLTL_OP_PT_CONFIGURE    = 0b01110,
    R2U2_MLTL_OP_PT_LOAD         = 0b01101,
    R2U2_MLTL_OP_PT_RETURN       = 0b01100,

    R2U2_MLTL_OP_PT_ONCE         = 0b01011,
    R2U2_MLTL_OP_PT_HISTORICALLY = 0b01010,
    R2U2_MLTL_OP_PT_SINCE        = 0b01001,
    R2U2_MLTL_OP_PT_LOCK         = 0b01000,

    R2U2_MLTL_OP_PT_NOT          = 0b00111,
    R2U2_MLTL_OP_PT_AND          = 0b00110,
    R2U2_MLTL_OP_PT_OR           = 0b00101,
    R2U2_MLTL_OP_PT_IMPLIES      = 0b00100,

    R2U2_MLTL_OP_PT_NAND         = 0b00011,
    R2U2_MLTL_OP_PT_NOR          = 0b00010,
    R2U2_MLTL_OP_PT_XOR          = 0b00001,
    R2U2_MLTL_OP_PT_EQUIVALENT   = 0b00000,
} r2u2_mltl_opcode_t;

typedef enum {
    R2U2_FT_OP_DIRECT      = 0b01,
    R2U2_FT_OP_ATOMIC      = 0b00,
    R2U2_FT_OP_SUBFORMULA  = 0b10,
    R2U2_FT_OP_NOT_SET     = 0b11
} r2u2_mltl_operand_type_t;

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
