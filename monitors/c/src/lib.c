#include "internals/config.h"
#include "r2u2.h"
#include "internals/debug.h"
#include "internals/process_binary.h"
#include "engines/engines.h"

#if R2U2_DEBUG
FILE* r2u2_debug_fptr = NULL;
#endif

r2u2_monitor_t r2u2_get_monitor(uint8_t* spec, r2u2_status_t* status) {
    /* Default config */
    r2u2_monitor_t monitor = R2U2_DEFAULT_MONITOR;

    // Populate instruction table from binary spec in instruction memory
    if (r2u2_process_binary(spec, &monitor) != R2U2_OK) {
      *status = R2U2_BAD_SPEC;
    } else {
      *status = R2U2_OK;
    }
    return monitor;
}

r2u2_status_t r2u2_update_binary_file(uint8_t* spec, r2u2_monitor_t* monitor) {
    // Memory resets....
    r2u2_monitor_reset(monitor);

    // Populate instruction table from binary spec in instruction memory
    if (r2u2_process_binary(spec, monitor) != R2U2_OK) {
      return R2U2_BAD_SPEC;
    }

    return R2U2_OK;
}

r2u2_status_t r2u2_monitor_step(r2u2_monitor_t* monitor){
  return r2u2_step(monitor);
}
