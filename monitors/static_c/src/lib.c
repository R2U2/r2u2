#include "internals/errors.h"
#include "r2u2.h"
#include <stdio.h>

#include "engines/binary_load.h"

#if R2U2_DEBUG
FILE* r2u2_debug_fptr = NULL;
#endif

r2u2_status_t r2u2_init(r2u2_monitor_t *monitor) {
    /* Default config and run */

    // Memory resets....
    r2u2_monitor_clock_reset(monitor);

    // Populate instruction table from binary spec in instruction memory
    if (r2u2_process_binary(monitor) != R2U2_OK) {
      return R2U2_BAD_SPEC;
    }

    return R2U2_OK;
}


r2u2_status_t r2u2_run(r2u2_monitor_t *monitor){
  r2u2_status_t err_cond;

  do {
    err_cond = r2u2_step(monitor);
  } while (err_cond == R2U2_OK);

  return err_cond;
}

r2u2_status_t r2u2_tic(r2u2_monitor_t *monitor){
  r2u2_status_t err_cond;
  r2u2_time start_time = monitor->time_stamp;

  do {
    err_cond = r2u2_step(monitor);
  } while ((monitor->time_stamp == start_time) && (err_cond == R2U2_OK));

  return err_cond;
}

r2u2_status_t r2u2_spin(r2u2_monitor_t *monitor){
  r2u2_status_t err_cond;

  do {
    err_cond = r2u2_step(monitor);
  } while ((monitor->prog_count != 0) && (err_cond == R2U2_OK));

  return err_cond;
}

r2u2_status_t r2u2_step(r2u2_monitor_t *monitor){
  r2u2_status_t err_cond;

  err_cond = r2u2_instruction_dispatch(monitor);

  return err_cond;
}
