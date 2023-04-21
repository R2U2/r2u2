#include "memory/monitor.h"

// As Java as this looks, our external API to rely on variable access

void r2u2_monitor_clock_reset(r2u2_monitor_t *monitor) {
  // TODO(bckempa): Should this be inline?
  monitor->time_stamp = 0;
  monitor->prog_count = 0;
  monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP;
}


// size_t r2u2_monitor_size(r2u2_monitor_t *monitor) {
//   return sizeof(*monitor);
// }
