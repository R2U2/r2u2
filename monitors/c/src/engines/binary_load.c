#include "binary_load.h"
#include "internals/bounds.h"
#include "internals/debug.h"
#include "internals/errors.h"
#include "instructions/booleanizer.h"
#include "engines/booleanizer.h"
#include "engines/mltl.h"
#include "engines/engines.h"

#include <stdio.h>

static short x = 0x3210;
#define BIG_ENDIAN ( *((char*) &x) == 0x32)

static void SwapBytes(uint8_t* data, int length){
  R2U2_TRACE_PRINT("Before swapping endianness: ");
  for(int x = 0; x < length; x++){
    R2U2_TRACE_PRINT("%d ", data[x]);
  }
  R2U2_TRACE_PRINT("\n");
  uint8_t temp;
  for(int i = 0; i < length/2; i++){
    temp = data[i];
    data[i] = data[length - 1 - i];
    data[length - 1 - i] = temp;
  }
  R2U2_TRACE_PRINT("After swapping endianness: ");
  for(int x = 0; x < length; x++){
    R2U2_TRACE_PRINT("%d ", data[x]);
  }
  R2U2_TRACE_PRINT("\n");
}

r2u2_status_t r2u2_process_binary(uint8_t* spec, r2u2_monitor_t *monitor) {
  size_t offset = 0;

  // Header Check:
  // TODO(bckempa): Version checks, report hash, parity, etc.
  R2U2_DEBUG_PRINT("Spec Info:\n\t%s\n",  &(spec[1]));
  offset = spec[0];

  // TODO(bckempa): Double check, size_t should always fit?
  for (size_t i=0; (spec[offset] != 0); offset += spec[offset]) {
    // TODO(bckempa): Until engines.c is refactored to separate raw dispatch
    // from monitor state transform, we'll look for config commands here.
    // Currently, only MLTL needs config commands, so we'll just check
    if ((spec[offset+1] == R2U2_ENG_CG) && (spec[offset+2] == R2U2_ENG_TL)) {
      if (BIG_ENDIAN) {
        // Big Endian target; therefore, swap bytes
        SwapBytes(&spec[offset+3], 4); // op1_value
        SwapBytes(&spec[offset+7], 4); // op2_value
        SwapBytes(&spec[offset+11], 4); // memory_reference
        // No need to swap bytes for op1_type, op2_type, and opcode since it is only one byte
      }
      // Process configuration command
      if (r2u2_mltl_instruction_dispatch(monitor,  (r2u2_mltl_instruction_t *) &(spec[offset+3])) != R2U2_OK) {
        // TODO(bckempa): Better error handling with logging here
        return R2U2_ERR_OTHER;
      }
    } else {
      if(spec[offset+1] == R2U2_ENG_BZ){
        r2u2_bz_instruction_t instr = r2u2_bz_set_from_binary(&(spec[offset+2]));
        // Special case: ICONST and FCONST only need to be run once since they load constants
        if (instr.opcode == R2U2_BZ_OP_ICONST){
          (monitor->value_buffer)[instr.memory_reference].i = r2u2_bz_get_param1_int_from_binary(&(spec[offset+2]));
          R2U2_DEBUG_PRINT("\tBZ ICONST\n");
          R2U2_DEBUG_PRINT("\tb%d = %d\n", instr.memory_reference, (monitor->value_buffer)[instr.memory_reference].i);
        }
        else if (instr.opcode == R2U2_BZ_OP_FCONST) {
          (monitor->value_buffer)[instr.memory_reference].f = r2u2_bz_get_param1_float_from_binary(&(spec[offset+2]));
          R2U2_DEBUG_PRINT("\tBZ FCONST\n");
          R2U2_DEBUG_PRINT("\tb%d = %lf\n", instr.memory_reference, (monitor->value_buffer)[instr.memory_reference].f);
        }
        else {
          // Store booleanizer instruction in table
          (monitor->bz_instruction_tbl)[monitor->bz_program_count.max_program_count] = instr;
          monitor->bz_program_count.max_program_count++;
        }
      }
      else if (spec[offset+1] == R2U2_ENG_TL){
        if (BIG_ENDIAN) {
          // Big Endian target; therefore, swap bytes
          SwapBytes(&spec[offset+2], 4); // op1_value
          SwapBytes(&spec[offset+6], 4); // op2_value
          SwapBytes(&spec[offset+10], 4); // memory_reference
          // No need to swap bytes for op1_type, op2_type, and opcode since they are only one byte
        }
        // Store temporal logic instruction in table
        (monitor->mltl_instruction_tbl)[monitor->mltl_program_count.max_program_count] = *((r2u2_mltl_instruction_t *) &(spec[offset+2]));
        monitor->mltl_program_count.max_program_count++;
      }
    }
  }

  return R2U2_OK;
}
