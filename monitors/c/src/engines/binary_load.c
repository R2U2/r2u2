#include "binary_load.h"
#include "engines.h"
#include "instruction.h"
#include "internals/bounds.h"
#include "internals/debug.h"
#include "internals/errors.h"
#include "engines/booleanizer.h"
#include "engines/mltl.h"
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

r2u2_status_t r2u2_process_binary(r2u2_monitor_t *monitor) {

  // Alias for readability:
  //  pc (for Program Counter) maps to instruction table entries
  //  data maps to raw bytes of inst mem loaded with binary
  r2u2_instruction_t* pc = *monitor->instruction_tbl;
  uint8_t* data = *monitor->instruction_mem;
  size_t offset = 0;

  // Header Check:
  // TODO(bckempa): Version checks, report hash, parity, etc.
  R2U2_DEBUG_PRINT("Spec Info:\n\t%s\n",  &(data[1]));
  offset = data[0];

  // TODO(bckempa): Double check, size_t should always fit?
  for (size_t i=0; (data[offset] != 0); offset += data[offset]) {
    // TODO(bckempa): Until engines.c is refactored to separate raw dispatch
    // from monitor state transform, we'll look for config commands here.
    // Currently, only MLTL needs config commands, so we'll just check
    if ((data[offset+1] == R2U2_ENG_CG) && (data[offset+2] == R2U2_ENG_TL)) {
        if (BIG_ENDIAN) {
          // Big Endian target; therefore, swap bytes
          SwapBytes(&data[offset+3], 4); // op1_value
          SwapBytes(&data[offset+7], 4); // op2_value
          SwapBytes(&data[offset+11], 4); // memory_reference
          // No need to swap bytes for op1_type, op2_type, and opcode since it is only one byte
        }
      
      // Process configuration command
      if (r2u2_mltl_instruction_dispatch(monitor,  (r2u2_mltl_instruction_t *) &(data[offset+3])) != R2U2_OK) {
        // TODO(bckempa): Better error handling with logging here
        return R2U2_ERR_OTHER;
      }
    } else {
      if(data[offset+1] == R2U2_ENG_BZ){
        r2u2_bz_instruction_t* instr = (r2u2_bz_instruction_t *) &(data[offset+2]);
        if (BIG_ENDIAN) {
          // Big Endian target; therefore, swap bytes
          if (instr->opcode == R2U2_BZ_OP_FCONST)
            SwapBytes(&data[offset+2], 8); // param1 - bz_float
          else
            SwapBytes(&data[offset+2], 4); // param1 - bz_addr or bz_int
          SwapBytes(&data[offset+10], 4); // param2
          SwapBytes(&data[offset+14], 4); // memory_reference
          // No need to swap bytes for opcode since it is only one byte
        }
        // Special case: ICONST and FCONST only need to be run once since they load constants
        if (instr->opcode == R2U2_BZ_OP_ICONST){
          (*monitor->value_buffer)[instr->memory_reference].i = instr->param1.bz_int;
          R2U2_DEBUG_PRINT("\tBZ ICONST\n");
          R2U2_DEBUG_PRINT("\tb%d = %d\n", instr->memory_reference, instr->param1.bz_int);
        }
        else if (instr->opcode == R2U2_BZ_OP_FCONST) {
          (*monitor->value_buffer)[instr->memory_reference].f = instr->param1.bz_float;
          R2U2_DEBUG_PRINT("\tBZ FCONST\n");
          R2U2_DEBUG_PRINT("\tb%d = %lf\n", instr->memory_reference, instr->param1.bz_float);
        }
        else {
          // Store booleanizer instruction in table
          pc[i++] = (r2u2_instruction_t){data[offset+1], &(data[offset+2])};
        }
      }
      else if (data[offset+1] == R2U2_ENG_TL){
        if (BIG_ENDIAN) {
          // Big Endian target; therefore, swap bytes
          SwapBytes(&data[offset+2], 4); // op1_value
          SwapBytes(&data[offset+6], 4); // op2_value
          SwapBytes(&data[offset+10], 4); // memory_reference
          // No need to swap bytes for op1_type, op2_type, and opcode since they are only one byte
        }
        // Store temporal logic instruction in table
        pc[i++] = (r2u2_instruction_t){data[offset+1], &(data[offset+2])};
      } else {
        // Store instruction metadata in table
        pc[i++] = (r2u2_instruction_t){data[offset+1], &(data[offset+2])};
      }
    }
  }

  return R2U2_OK;
}
