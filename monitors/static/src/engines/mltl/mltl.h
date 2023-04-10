#ifndef R2U2_ENGINES_MLTL_H
#define R2U2_ENGINES_MLTL_H

#include "r2u2.h"

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

    R2U2_MLTL_OP_FT_NAND         = 0b10011,
    R2U2_MLTL_OP_FT_NOR          = 0b10010,
    R2U2_MLTL_OP_FT_XOR          = 0b10001,
    R2U2_MLTL_OP_FT_EQUIVALENT   = 0b10000,


    // Future Tense: 1xxxx

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
// data structure for operand
// not packed
//
typedef struct {
    r2u2_mltl_operand_type_t  opnd_type;
    uint8_t value;
} r2u2_mltl_operand_t;

//
// data structure for instruction
// not packed
// instruction format for packed representation:
//  OPC:5 op1:10 op2:10 intvl:8 scratch:7
//
typedef struct {
    r2u2_mltl_opcode_t    opcode;
    r2u2_mltl_operand_t   op1;
    r2u2_mltl_operand_t   op2;
    size_t memory_reference;
} r2u2_mltl_instruction_t;

// data structure for address info of SCQ
typedef struct {
    uint16_t start_addr;
    uint16_t end_addr;
}   r2u2_mltl_addr_SCQ_t;

//
// data type for
// buffer head or tail distinction
//
typedef enum {
    dontcare = 0,
    tail = 1,
    head = 2
} r2u2_mltl_head_or_tail_t;

//
// interval memory for intervals (not packed)
// LB:16 UB:16
//
typedef uint16_t interval_bound_t;
typedef struct {
    interval_bound_t    lb;
    interval_bound_t    ub;
} r2u2_mltl_interval_t;


r2u2_status_t r2u2_mltl_instruction_dispatch(r2u2_monitor_t *, r2u2_mltl_instruction_t *);

#endif /* R2U2_ENGINES_MLTL_H */
