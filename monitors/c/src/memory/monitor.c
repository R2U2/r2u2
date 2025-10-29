#include "monitor.h"
#include <string.h>

void r2u2_monitor_clock_reset(r2u2_monitor_t* monitor) {
  monitor->time_stamp = 0;
  monitor->bz_program_count.curr_program_count = 0;
  monitor->mltl_program_count.curr_program_count = 0;
  monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
}

void r2u2_monitor_reset(r2u2_monitor_t* monitor) {
  r2u2_monitor_clock_reset(monitor);
  monitor->bz_program_count.max_program_count = 0;
  monitor->mltl_program_count.max_program_count = 0;
  // WARNING: The following assumes that R2U2_DEFAULT_MONITOR is utilized!
  memset(monitor->queue_arena.queue_mem, 0, sizeof(r2u2_verdict) * (R2U2_MAX_QUEUE_SLOTS + (R2U2_MAX_TEMPORAL_OPERATORS * R2U2_TEMPORAL_METADATA_SIZE)));
}