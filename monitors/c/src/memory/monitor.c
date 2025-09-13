#include "memory/monitor.h"
#include <string.h>

void r2u2_monitor_clock_reset(r2u2_monitor_t *monitor) {
  monitor->time_stamp = 0;
  monitor->bz_program_count.curr_program_count = 0;
  monitor->mltl_program_count.curr_program_count = 0;
  monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
  memset(monitor->queue_arena.queue_mem, 0, sizeof(r2u2_verdict) * R2U2_TOTAL_QUEUE_SLOTS);
}

void r2u2_monitor_reset(r2u2_monitor_t *monitor) {
  monitor->time_stamp = 0;
  monitor->bz_program_count.curr_program_count = 0;
  monitor->bz_program_count.max_program_count = 0;
  monitor->mltl_program_count.curr_program_count = 0;
  monitor->mltl_program_count.max_program_count = 0;
  monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
  memset(monitor->queue_arena.queue_mem, 0, sizeof(r2u2_verdict) * R2U2_TOTAL_QUEUE_SLOTS);
}