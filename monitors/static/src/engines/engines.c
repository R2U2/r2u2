#include "internals/errors.h"
#include "r2u2.h"

#include <stdio.h>
#include <string.h> // For memcpy

#include "engines/engines.h"
#include "engines/atomic_checker/atomic_checker.h"
#include "engines/booleanizer/booleanizer.h"
#include "engines/mltl/mltl.h"

#include "memory/register.h" // For buffer flip
// r2u2_status_t (*r2u2_engine_func_table[])(r2u2_instruction_t *) = {

// };

// TODO(bckempa): This should be refactored to seperate out the raw dispatch
// case statement for use by immediate commands in binary_load.c
//
// Assumption: Program counter points at next instruction to execute
r2u2_status_t r2u2_instruction_dispatch(r2u2_monitor_t *monitor) {
    r2u2_status_t error_cond;

    R2U2_DEBUG_PRINT("%d.%zu.%d\n",monitor->time_stamp, monitor->prog_count, monitor->progress);
    switch ((*monitor->instruction_tbl)[monitor->prog_count].engine_tag) {
      case R2U2_ENG_NA: {
        R2U2_DEBUG_PRINT("\n");

        switch (monitor->progress) {
          // Yes two of these cases are identical - the compiler will optimize
          case R2U2_MONITOR_PROGRESS_FIRST_LOOP: {
            // First pass complete, rerun program counter to check for progress
            monitor->prog_count = 0;
            monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS;
            break;
          }
          case R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS: {
            // Progress made this loop, rerun program counter
            monitor->prog_count = 0;
            monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS;
            break;
          }
          case R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS: {
            // End of timestep - setup for next step

            #if R2U2_DEBUG
            // Debug print atomics at end of timestep
            R2U2_TRACE_PRINT("ATM VEC ADDR: [%p]\tATM BUF ADDR: [%p]\n", monitor->atomic_buffer[0], monitor->atomic_buffer[1]);
            R2U2_DEBUG_PRINT("Atomic Vector:\n[");
            for (int i=0; i < R2U2_MAX_ATOMICS-1; ++i) {
              R2U2_DEBUG_PRINT("%d, ", (*(monitor->atomic_buffer[0]))[i]);
            }
            R2U2_DEBUG_PRINT("%d]\n", (*(monitor->atomic_buffer[0]))[R2U2_MAX_ATOMICS-1]);
            #endif

            #if R2U2_DEBUG
            // Debug print PT results at end of timestep
            R2U2_DEBUG_PRINT("Past Time Results:\n[");
            for (int i=0; i < R2U2_MAX_INSTRUCTIONS-1; ++i) {
              R2U2_DEBUG_PRINT("%d, ", (*(monitor->past_time_result_buffer[0]))[i]);
            }
            R2U2_DEBUG_PRINT("%d]\n", (*(monitor->past_time_result_buffer[0]))[R2U2_MAX_INSTRUCTIONS-1]);
            #endif

            // Flip buffered Vectors
            // TODO(bckempa): what about mod2 indexing to select A/B side?
            // memcpy(monitor->atomic_buffer[1], monitor->atomic_buffer[0], sizeof(r2u2_atomic_buffer_t));
            // memcpy(monitor->past_time_result_buffer[1], monitor->past_time_result_buffer[0], sizeof(r2u2_atomic_buffer_t));
            r2u2_atomic_vector_flip(monitor->atomic_buffer);
            r2u2_atomic_vector_flip(monitor->past_time_result_buffer);


            // Update Vector Clock for next timestep
            monitor->time_stamp++;
            monitor->prog_count = 0;
            monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
            break;
          }
        }

        return R2U2_OK; // Early return to keep program counter at 0
      }
      case R2U2_ENG_SY: {
        R2U2_DEBUG_PRINT("Got SY Inst\n");
        error_cond = R2U2_OK;
        break;
      }
      case R2U2_ENG_CG: {
        // This header should be stripped before you get here, but we'll
        // silently allow this for now in case of weird bin layouts
        // TODO(bckempa): Debug only warning for config cmds at non-zero time
        error_cond = R2U2_OK;
        break;
      }
      case R2U2_ENG_AT: {
        // Only process AT once per timestep
        if (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP) {
          error_cond = r2u2_at_instruction_dispatch(monitor, (r2u2_at_instruction_t*)(*monitor->instruction_tbl)[monitor->prog_count].instruction_data);
        } else {
          error_cond = R2U2_OK;
        }
        break;
      }
      case R2U2_ENG_TL: {
        error_cond = r2u2_mltl_instruction_dispatch(monitor, (r2u2_mltl_instruction_t*)(*monitor->instruction_tbl)[monitor->prog_count].instruction_data);
        break;
      }
      case R2U2_ENG_BZ: {
        error_cond = r2u2_bz_instruction_dispatch(monitor, (r2u2_bz_instruction_t*)(*monitor->instruction_tbl)[monitor->prog_count].instruction_data);
        break;
      }
      default: {
          return R2U2_ERR_OTHER;
      }
    }

    // Standard return increments PC, any other action like resets return early
    monitor->prog_count++;
    return error_cond;
}
