#include "internals/config.h"
#include "process_binary.h"
#include "internals/debug.h"
#include "internals/bounds.h"
#include "engines/booleanizer.h"
#include "engines/mltl.h"
#include "engines/engines.h"
#include <string.h>

r2u2_status_t r2u2_process_binary(uint8_t* spec, r2u2_monitor_t *monitor) {
  size_t offset = 0;

  // Header Check:
  R2U2_DEBUG_PRINT("Spec Info:\n\t%s\n",  &(spec[1]));
  offset = spec[0];

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

  // Iterate through mltl table
  r2u2_scq_control_block_t *ctrl;
  for (size_t i=0; i < monitor->mltl_program_count.max_program_count; i++){
    r2u2_mltl_instruction_t instr = (monitor->mltl_instruction_tbl)[i];
    // For future time, we never need information from [0, lb]
    if((monitor->mltl_instruction_tbl)[i].opcode == R2U2_MLTL_OP_UNTIL || 
        (monitor->mltl_instruction_tbl)[i].opcode == R2U2_MLTL_OP_RELEASE){
          ctrl = &(monitor->queue_arena.control_blocks[i]);
          (*ctrl).next_time = (*ctrl).temporal_block.lower_bound;
        }
  }

  #if R2U2_AUX_STRING_SPECS
    char type;
    size_t aux_formula_num = 0;
    size_t aux_contract_num = 0;
    int length = 0;
    r2u2_aux_info_arena_t *aux_arena = &(monitor->aux_info_arena);
    (aux_arena->formula_control_blocks)[0].spec_str = aux_arena->aux_mem;

    do {
      // Length encodes size of processed string not including null
      // so we move forwrod by length +1 to jump each string
      // This initial 0 + 1 moves us past the final zero offset of the inst mem
      // if length is zero at the end of a loop, nothing was found so search ends
      offset += length + 1;
      if (sscanf((char*)&(spec[offset]), "%c", &type) == 1) {
        switch(type){
          case 'C': {
            if (aux_contract_num == 0){ // All formulas always appear in binary before contracts
              (aux_arena->contract_control_blocks)[0].spec_str = (aux_arena->formula_control_blocks)[aux_formula_num-1].spec_str + strlen((aux_arena->formula_control_blocks)[aux_formula_num-1].spec_str) + 1; // Leave a Null
            }
            sscanf((char*)&(spec[offset]), "%*c %s %u %u %u%n", (aux_arena->contract_control_blocks)[aux_contract_num].spec_str, &(aux_arena->contract_control_blocks[aux_contract_num].spec_0), &(aux_arena->contract_control_blocks[aux_contract_num].spec_1), &(aux_arena->contract_control_blocks[aux_contract_num].spec_2), &length);
            if (R2U2_MAX_CONTRACTS > (aux_contract_num + 1)){
              (aux_arena->contract_control_blocks)[aux_contract_num+1].spec_str = (aux_arena->contract_control_blocks)[aux_contract_num].spec_str + strlen((aux_arena->contract_control_blocks)[aux_contract_num].spec_str) + 1; // Leave a Null
            }
            R2U2_DEBUG_PRINT("Mapping contract: %s\n", (aux_arena->contract_control_blocks)[aux_contract_num].spec_str);
            aux_contract_num++;
            break;
          }
          case 'F': {
            sscanf((char*)&(spec[offset]), "%*c %s %u%n", (aux_arena->formula_control_blocks)[aux_formula_num].spec_str, &(aux_arena->formula_control_blocks[aux_formula_num].spec), &length);
            if (R2U2_MAX_FORMULAS > (aux_formula_num + 1)){
              (aux_arena->formula_control_blocks)[aux_formula_num+1].spec_str = (aux_arena->formula_control_blocks)[aux_formula_num].spec_str + strlen((aux_arena->formula_control_blocks)[aux_formula_num].spec_str) + 1; // Leave a Null
            }
            R2U2_DEBUG_PRINT("Mapping formula: %s\n", (aux_arena->formula_control_blocks)[aux_formula_num].spec_str);
            aux_formula_num++;
            break;
          }
          default: {
            R2U2_DEBUG_PRINT("Aux: Invalid type '%c' - end of search\n", type);
            length = 0;
            break;
          }
        }
      } else {
          // Error scanning type char, end search
          R2U2_DEBUG_PRINT("Aux: Cannot read type end of search\n");
          length = 0;
      }
    } while (length != 0);

    aux_arena->max_aux_formula = aux_formula_num;
    aux_arena->max_aux_contract = aux_contract_num;
    R2U2_DEBUG_PRINT("Loaded %zu auxiliary data (%zu formulas and %zu contracts)\n", aux_formula_num + aux_contract_num, aux_formula_num, aux_contract_num);
  #endif

  return R2U2_OK;
}
