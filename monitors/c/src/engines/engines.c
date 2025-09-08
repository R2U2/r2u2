#include "internals/errors.h"
#include "r2u2.h"


#include <stdio.h>
#include <string.h> // For memcpy

#include "engines/engines.h"
#include "engines/booleanizer.h"
#include "engines/mltl.h"

r2u2_status_t r2u2_instruction_dispatch(r2u2_monitor_t *monitor) {
    r2u2_status_t error_cond;

    R2U2_DEBUG_PRINT("%d.%zu.%d\n",monitor->time_stamp, monitor->prog_count, monitor->progress);
    while(monitor->bz_program_count.curr_program_count < monitor->bz_program_count.max_program_count){
      error_cond = r2u2_bz_instruction_dispatch(monitor, &(monitor->bz_instruction_tbl)[monitor->bz_program_count.curr_program_count]);
      monitor->bz_program_count.curr_program_count++;
    }
    monitor->bz_program_count.curr_program_count = 0;

    r2u2_time start_time = monitor->time_stamp;
    while(start_time == monitor-> time_stamp){
       while(monitor->mltl_program_count.curr_program_count < monitor->mltl_program_count.max_program_count){
        error_cond = r2u2_mltl_instruction_dispatch(monitor, &(monitor->mltl_instruction_tbl)[monitor->mltl_program_count.curr_program_count]);
        monitor->mltl_program_count.curr_program_count++;
      }
      switch (monitor->progress) {
        case R2U2_MONITOR_PROGRESS_FIRST_LOOP: {
          // First pass complete, rerun program counter to check for progress
          monitor->mltl_program_count.curr_program_count= 0;
          monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS;
          break;
        }
        case R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS: {
          // Progress made this loop, rerun program counter
          monitor->mltl_program_count.curr_program_count= 0;
          monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS;
          break;
        }
        case R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS: {
          // End of timestep - setup for next step

          #if R2U2_DEBUG
          // Debug print atomics at end of timestep
          R2U2_TRACE_PRINT("ATM VEC ADDR: [%p]\n", monitor->atomic_buffer);
          R2U2_DEBUG_PRINT("Atomic Vector:\n[");
          for (int i=0; i < R2U2_MAX_ATOMICS-1; ++i) {
            R2U2_DEBUG_PRINT("%d, ", (monitor->atomic_buffer)[i]);
          }
          R2U2_DEBUG_PRINT("%d]\n", (monitor->atomic_buffer)[R2U2_MAX_ATOMICS-1]);
          #endif

          // Update Vector Clock for next timestep
          monitor->time_stamp++;
          monitor->mltl_program_count.curr_program_count= 0;
          monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
          break;
        }
    }
  }
    return error_cond;
}
