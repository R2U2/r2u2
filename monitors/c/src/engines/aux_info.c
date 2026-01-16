#include "aux_info.h"
#include "../internals/config.h"
#include <stdio.h>

r2u2_status_t r2u2_aux_formula_report(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t instr, r2u2_verdict result){
#if R2U2_AUX_STRING_SPECS
  r2u2_aux_info_arena_t aux_arena = monitor->aux_info_arena;
  if (instr.op2_value < aux_arena.max_aux_formula){
    fprintf(monitor->out_file, "%s:%u,%s\n", aux_arena.formula_control_blocks[instr.op2_value].spec_str, get_verdict_time(result), get_verdict_truth(result) ? "T" : "F");
  } else {
    fprintf(monitor->out_file, "%u:%u,%s\n", instr.op2_value, get_verdict_time(result), get_verdict_truth(result) ? "T" : "F");
  }
#endif
  return R2U2_OK;
}

r2u2_status_t r2u2_aux_contract_report(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t instr, r2u2_verdict result){
#if R2U2_AUX_STRING_SPECS
  r2u2_aux_info_arena_t aux_arena = monitor->aux_info_arena;
  for (size_t i = 0; i < aux_arena.max_aux_contract; i++) {
    if (instr.op2_value == aux_arena.contract_control_blocks[i].spec_0 && !(get_verdict_truth(result))){
      fprintf(monitor->out_file, "Contract %s inactive at %d\n", aux_arena.contract_control_blocks[i].spec_str, get_verdict_time(result));
      break;
    } else if (instr.op2_value == aux_arena.contract_control_blocks[i].spec_1 && !(get_verdict_truth(result))){
      fprintf(monitor->out_file, "Contract %s invalid at %d\n", aux_arena.contract_control_blocks[i].spec_str, get_verdict_time(result));
      break;
    } else if (instr.op2_value == aux_arena.contract_control_blocks[i].spec_2 && get_verdict_truth(result)){
      fprintf(monitor->out_file, "Contract %s verified at %d\n", aux_arena.contract_control_blocks[i].spec_str, get_verdict_time(result));
      break;
    }
  }
#endif
  return R2U2_OK;
}