#include "binary_load.h"
#include "internals/bounds.h"
#include "internals/debug.h"
#include "internals/errors.h"
#include "instructions/booleanizer.h"
#include "engines/booleanizer.h"
#include "engines/mltl.h"
#include "engines/engines.h"

#include <stdio.h>

r2u2_status_t r2u2_process_binary(uint8_t* spec, r2u2_monitor_t *monitor) {
  size_t offset = 0;

  // Header Check:
  // TODO(bckempa): Version checks, report hash, parity, etc.
  R2U2_DEBUG_PRINT("Spec Info:\n\t%s\n",  &(spec[1]));
  offset = spec[0];

  // TODO(bckempa): Double check, size_t should always fit?
  for (size_t i=0; (spec[offset] != 0); offset += spec[offset]) {
    if ((spec[offset+1] == R2U2_ENG_CG) && (spec[offset+2] == R2U2_ENG_TL)) {
      // Process configuration command
      r2u2_mltl_instruction_t instr = r2u2_mltl_set_from_binary(&(spec[offset+3]));
      if (r2u2_mltl_configure_instruction_dispatch(monitor, &instr) != R2U2_OK) {
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
          // Store temporal logic instruction in table
          (monitor->mltl_instruction_tbl)[monitor->mltl_program_count.max_program_count] = r2u2_mltl_set_from_binary(&(spec[offset+2]));
          monitor->mltl_program_count.max_program_count++;
        }
    }
  }

  return R2U2_OK;
}
