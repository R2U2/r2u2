#ifndef R2U2_MEMORY_MONITOR_H
#define R2U2_MEMORY_MONITOR_H

#include <stdio.h> // Used for file type

// A "Header-only" library, contains modification functions for associated type
#include "internals/types.h"
#include "instructions/booleanizer.h"
#include "instructions/mltl.h"

#include "memory/register.h"
#include "memory/shared_connection_queue.h"

typedef enum {
  R2U2_MONITOR_PROGRESS_FIRST_LOOP,
  R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS,
  R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS,
} r2u2_monitor_progress_state_t;

// Monitor is defined with pointers to avoid forcing a size on arrays, but
// hopefully you keep them close-by so the cache hits. By default this should
// all end up in BBS
typedef struct {
  // Vector clock state
  r2u2_time time_stamp; //
  r2u2_monitor_progress_state_t progress; // TODO(bckempa): Track value in debug
  size_t    prog_count; // TODO(bckempa): type justification and bounds check

  // Specification Instructions
  r2u2_instruction_memory_t  *instruction_mem;
  r2u2_instruction_table_t *instruction_tbl;

  // Output handlers
  FILE *out_file;         // R2U2 Logfile pointer, always written if not NULL
  r2u2_status_t (*out_func)(r2u2_instruction_t, r2u2_verdict*); // R2U2 output callback pointer, used if not NULL
  // TODO(bckempa): Set callback type

  // Memory domain pointers
  // Use pointers instead of direct members because:
  //  1) consistent monitor size independent of domain size
  //  2) allow uses like memory-mapped DMA regions
  // Buffers are already just pairs of pointers, so we use those directly
  // TODO(bckempa): Can that be more transparent/ergonomic?
  r2u2_signal_vector_t    *signal_vector;
  r2u2_value_buffer_t     *value_buffer;
  r2u2_atomic_buffer_t    *atomic_buffer;
  r2u2_scq_arena_t       shared_connection_queue_mem;

} r2u2_monitor_t;

// Shortcut for getting a monitor of predefined extents
// Should only be used at file scope because:
//  1) C99 compound literals are used for memory domains and adopt enclosing scope
//     unless at file scope, where they get static lifetime
//  2) Want to ensure placement in BBS program segment
//
// TODO(bckempa): Can we use the typedef for the initialization instead?
#define R2U2_DEFAULT_MONITOR \
  { \
    0, 0, 0, \
    &(uint8_t [R2U2_MAX_INST_LEN]){0}, \
    &(r2u2_instruction_t [R2U2_MAX_INSTRUCTIONS]){0}, \
    NULL, NULL, \
    &(void*[R2U2_MAX_SIGNALS]){0}, \
    &(r2u2_value_t [R2U2_MAX_BZ_INSTRUCTIONS]){0}, \
    &(r2u2_bool [R2U2_MAX_ATOMICS]){0}, \
    {NULL, NULL}, \
  }


// As Java as this looks, our external API shouldn't rest on variable access

/// @brief      Resets the monitors vector clock without changing other state
/// @param[in]  monitor  Pointer to r2u2_monitor_t
/// @return     None
void r2u2_monitor_clock_reset(r2u2_monitor_t *monitor);

#endif /* R2U2_MEMORY_MONITOR_H */
