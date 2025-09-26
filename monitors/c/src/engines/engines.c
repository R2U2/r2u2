
#include "engines.h"
#include "booleanizer.h"
#include "mltl.h"
#include "../internals/debug.h"

r2u2_status_t r2u2_step(r2u2_monitor_t* monitor) {
    r2u2_status_t error_cond;

    // Operate over all BZ instructions first and only once on each step forward
    R2U2_DEBUG_PRINT("(BZ) %d.%zu\n",monitor->time_stamp, monitor->bz_program_count.curr_program_count);
    while(monitor->bz_program_count.curr_program_count < monitor->bz_program_count.max_program_count){
      error_cond = r2u2_bz_update(monitor);
      monitor->bz_program_count.curr_program_count++;
    }
    monitor->bz_program_count.curr_program_count = 0;

    // Operate over all MLTL instructions until no further progress is made
    r2u2_time start_time = monitor->time_stamp;
    while(start_time == monitor->time_stamp){
       while(monitor->mltl_program_count.curr_program_count < monitor->mltl_program_count.max_program_count){
        R2U2_DEBUG_PRINT("(TL) %d.%zu.%d\n",monitor->time_stamp, monitor->mltl_program_count.curr_program_count, monitor->progress);
        error_cond = r2u2_mltl_update(monitor);
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

          // Update clock for next timestep
          monitor->time_stamp++;
          monitor->mltl_program_count.curr_program_count = 0;
          monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
          break;
        }
    }
  }
    return error_cond;
}
