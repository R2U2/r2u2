#include "internals/config.h"
#include "r2u2.h"
#include "internals/debug.h"
#include "internals/process_binary.h"
#include "engines/engines.h"
#include <string.h>

#if R2U2_DEBUG
FILE* r2u2_debug_fptr = NULL;
#endif

r2u2_status_t r2u2_load_specification(uint8_t* spec, r2u2_monitor_t* monitor) {
    // Memory resets....
    r2u2_monitor_reset(monitor);

    // Populate instruction table from binary spec in instruction memory
    if (r2u2_process_binary(monitor, spec) != R2U2_OK) {
      return R2U2_BAD_SPEC;
    }

    return R2U2_OK;
}

r2u2_status_t r2u2_step(r2u2_monitor_t* monitor){
  return r2u2_engine_step(monitor);
}

void r2u2_load_bool_signal(r2u2_monitor_t* monitor, size_t index, r2u2_bool value){
  if (monitor->bz_program_count.max_program_count == 0) {
    monitor->atomic_buffer[index] = value;
  } else {
    monitor->signal_vector[index].i = (r2u2_int) value;
  }
}

void r2u2_load_int_signal(r2u2_monitor_t* monitor, size_t index, r2u2_int value){
  if (monitor->bz_program_count.max_program_count == 0) {
    monitor->atomic_buffer[index] = value != 0;
  } else {
    monitor->signal_vector[index].i = value;
  }
}

void r2u2_load_float_signal(r2u2_monitor_t* monitor, size_t index, r2u2_float value){
  if (monitor->bz_program_count.max_program_count == 0) {
    monitor->atomic_buffer[index] = value >= R2U2_FLOAT_EPSILON || value <= -R2U2_FLOAT_EPSILON;
  } else {
    monitor->signal_vector[index].f = value;
  }
}

void r2u2_load_string_signal(r2u2_monitor_t* monitor, size_t index, char* value){
  if (monitor->bz_program_count.max_program_count == 0) {
    monitor->atomic_buffer[index] = (strcmp(value,"0") != 0);
  } else {
    //Note that to be interpreted as a float, the string value must include a decimal point
    if (strchr(value, '.') != NULL){
      sscanf(value, "%lf", &(monitor->signal_vector[index].f));
    } else {
      sscanf(value, "%d", &(monitor->signal_vector[index].i));
    }
  }
}
