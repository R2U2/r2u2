#include "booleanizer.h"

r2u2_int r2u2_bz_get_param1_int_from_binary(uint8_t* spec) {
    return (r2u2_int)(spec[0] + (spec[1] << 8) + (spec[2] << 16) + (spec[3] << 24));
}

r2u2_float r2u2_bz_get_param1_float_from_binary(uint8_t* spec) {
    uint64_t temp_val = (spec[0] + (spec[1] << 8) + (spec[2] << 16) + (spec[3] << 24) +
                ((uint64_t)spec[4] << 32) + ((uint64_t)spec[5] << 40) + ((uint64_t)spec[6] << 48) + ((uint64_t)spec[7] << 56));
    r2u2_float val;
    memcpy(&val, &temp_val, 8);
    return val;
}

r2u2_bz_instruction_t r2u2_bz_set_from_binary(uint8_t* spec) {
    r2u2_bz_instruction_t instr; 
    instr.param1 = (uint32_t)(spec[0] + (spec[1] << 8) + (spec[2] << 16) + (spec[3] << 24));
    instr.param2 = (uint32_t)(spec[8] + (spec[9] << 8) + (spec[10] << 16) + (spec[11] << 24));
    instr.memory_reference = (uint32_t)(spec[12] + (spec[13] << 8) + (spec[14] << 16) + (spec[15] << 24));
    instr.opcode = spec[16];
    return instr;
}