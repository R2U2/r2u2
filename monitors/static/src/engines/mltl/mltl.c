#include "r2u2.h"

#include "mltl.h"
#include "future_time.h"
#include "past_time.h"

r2u2_status_t r2u2_mltl_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr) {

  // Copy to buffer to avoid alignment issues
  // TODO(bckempa): Make this optional based on bin packing switch
  r2u2_mltl_instruction_t inst_buff;
  memcpy(&inst_buff, instr, sizeof(r2u2_mltl_instruction_t));

  // Dispatch based on tense
  if (inst_buff.opcode & R2U2_MLTL_TENSE_FUTURE) { // TODO(bckempa): check with mltl.h constant
    return r2u2_mltl_ft_update(monitor, &inst_buff);
  } else if (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP) {
    // Only execute PT on first loop
    return r2u2_mltl_pt_update(monitor, &inst_buff);
  }

  return R2U2_OK;
}
