#include "mltl.h"

r2u2_mltl_instruction_t r2u2_mltl_set_from_binary(uint8_t* spec) {
    r2u2_mltl_instruction_t instr; 
    instr.op1_value = (uint32_t)(spec[0] + (spec[1] << 8) + (spec[2] << 16) + (spec[3] << 24));
    instr.op2_value = (uint32_t)(spec[4] + (spec[5] << 8) + (spec[6] << 16) + (spec[7] << 24));
    instr.memory_reference = (uint32_t)(spec[8] + (spec[9] << 8) + (spec[10] << 16) + (spec[11] << 24));
    instr.op1_type = spec[12];
    instr.op2_type = spec[13];
    instr.opcode = spec[14];
    return instr;
}