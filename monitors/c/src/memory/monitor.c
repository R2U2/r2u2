#include "memory/monitor.h"

void r2u2_monitor_clock_reset(r2u2_monitor_t *monitor) {
  monitor->time_stamp = 0;
  monitor->bz_program_count.curr_program_count = 0;
  monitor->mltl_program_count.curr_program_count = 0;
  monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
}