#include "r2u2.h"

#include "mltl.h"
#include "future_time.h"
#include "past_time.h"

r2u2_status_t r2u2_mltl_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr) {

  // Dispatch based on tense
  if (instr->opcode & 0b10000) { // TODO(bckempa): check with mltl.h constant
    return r2u2_mltl_ft_update(monitor, instr);
  } else if (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP) {
    // Only execute PT on first loop
    return r2u2_mltl_pt_update(monitor, instr);
  }

  return R2U2_OK;
}
