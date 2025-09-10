#include "internals/errors.h"
#include "r2u2.h"
#include <stdio.h>

#include "engines/binary_load.h"
#include "engines/engines.h"

#if R2U2_DEBUG
FILE* r2u2_debug_fptr = NULL;
#endif

r2u2_status_t r2u2_init(uint8_t* spec, r2u2_monitor_t *monitor) {
    /* Default config and run */

    // Memory resets....
    r2u2_monitor_reset(monitor);

    // Populate instruction table from binary spec in instruction memory
    if (r2u2_process_binary(spec, monitor) != R2U2_OK) {
      return R2U2_BAD_SPEC;
    }

    return R2U2_OK;
}

r2u2_status_t r2u2_step(r2u2_monitor_t *monitor){
  r2u2_status_t err_cond;

  err_cond = r2u2_instruction_dispatch(monitor);

  return err_cond;
}
