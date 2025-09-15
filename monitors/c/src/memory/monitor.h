#ifndef R2U2_MEMORY_MONITOR_H
#define R2U2_MEMORY_MONITOR_H

#include <stdio.h> // Used for file type

#include "internals/config.h"
#include "internals/types.h"
#if R2U2_AUX_STRING_SPECS
#include "instructions/aux_info.h"
#endif
#include "instructions/booleanizer.h"
#include "instructions/mltl.h"

#include "memory/shared_connection_queue.h"

typedef enum {
  R2U2_MONITOR_PROGRESS_FIRST_LOOP,
  R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS,
  R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS,
} r2u2_monitor_progress_state_t;

typedef struct program_count {
  size_t curr_program_count;
  size_t max_program_count;
} program_count_t;

typedef void* r2u2_signal_t;

// Monitor is defined with pointers to avoid forcing a size on arrays, but
// hopefully you keep them close-by so the cache hits. By default this should
// all end up in BBS
typedef struct r2u2_monitor {
  r2u2_time time_stamp;
  r2u2_monitor_progress_state_t progress;
  program_count_t bz_program_count;
  r2u2_bz_instruction_t *bz_instruction_tbl;
  program_count_t mltl_program_count;
  r2u2_mltl_instruction_t *mltl_instruction_tbl;

  // Output handlers
  FILE *out_file;         // R2U2 Logfile pointer, always written if not NULL
  r2u2_status_t (*out_func)(r2u2_mltl_instruction_t, r2u2_verdict*); // R2U2 output callback pointer, used if not NULL

  // Memory domain pointers
  // Use pointers instead of direct members because:
  //  1) consistent monitor size independent of domain size
  //  2) allow uses like memory-mapped DMA regions
  // Queue arena is already just pairs of pointers, so we use those directly
  r2u2_signal_t    *signal_vector;
  r2u2_value_t     *value_buffer;
  r2u2_bool    *atomic_buffer;
  #if R2U2_AUX_STRING_SPECS
  r2u2_aux_info_arena_t aux_info_arena;
  #endif
  r2u2_scq_arena_t        queue_arena;

} r2u2_monitor_t;

// Shortcut for getting a monitor of predefined extents
// Should only be used at file scope because:
//  1) C99 compound literals are used for memory domains and adopt enclosing scope
//     unless at file scope, where they get static lifetime
//  2) Want to ensure placement in BBS program segment
//
#if R2U2_AUX_STRING_SPECS
  #define R2U2_DEFAULT_MONITOR \
    { \
      .time_stamp = 0, \
      .progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP, \
      .bz_program_count = (program_count_t){0,0}, \
      .bz_instruction_tbl = (r2u2_bz_instruction_t [R2U2_MAX_BZ_INSTRUCTIONS]){0}, \
      .mltl_program_count = (program_count_t){0,0}, \
      .mltl_instruction_tbl = (r2u2_mltl_instruction_t [R2U2_MAX_TL_INSTRUCTIONS]){0}, \
      .out_file = NULL, \
      .out_func = NULL, \
      .signal_vector = (void*[R2U2_MAX_SIGNALS]){0}, \
      .value_buffer = (r2u2_value_t [R2U2_MAX_BZ_INSTRUCTIONS]){0}, \
      .atomic_buffer = (r2u2_bool [R2U2_MAX_ATOMICS]){0}, \
      .aux_info_arena = {(r2u2_formula_aux_info_t [R2U2_MAX_FORMULAS]){0}, (r2u2_contract_aux_info_t [R2U2_MAX_CONTRACTS]){0}, (char [R2U2_MAX_AUX_BYTES]) {0}, 0, 0}, \
      .queue_arena = {(r2u2_scq_control_block_t [R2U2_MAX_TL_INSTRUCTIONS]){0}, (r2u2_verdict [R2U2_TOTAL_QUEUE_SLOTS]){0}}, \
    }
#else
  #define R2U2_DEFAULT_MONITOR \
    { \
      .time_stamp = 0, \
      .progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP, \
      .bz_program_count = (program_count_t){0,0}, \
      .bz_instruction_tbl = (r2u2_bz_instruction_t [R2U2_MAX_BZ_INSTRUCTIONS]){0}, \
      .mltl_program_count = (program_count_t){0,0}, \
      .mltl_instruction_tbl = (r2u2_mltl_instruction_t [R2U2_MAX_TL_INSTRUCTIONS]){0}, \
      .out_file = NULL, \
      .out_func = NULL, \
      .signal_vector = (void*[R2U2_MAX_SIGNALS]){0}, \
      .value_buffer = (r2u2_value_t [R2U2_MAX_BZ_INSTRUCTIONS]){0}, \
      .atomic_buffer = (r2u2_bool [R2U2_MAX_ATOMICS]){0}, \
      .queue_arena = {(r2u2_scq_control_block_t [R2U2_MAX_TL_INSTRUCTIONS]){0}, (r2u2_verdict [R2U2_TOTAL_QUEUE_SLOTS]){0}}, \
    }
#endif

/// @brief      Resets the monitors vector clock and SCQ slots without changing other state
/// @param[in]  monitor  Pointer to r2u2_monitor_t
/// @return     None
void r2u2_monitor_clock_reset(r2u2_monitor_t* monitor);

/// @brief      Resets the monitors vector clock, SCQ slots, and instruction tables
/// @param[in]  monitor  Pointer to r2u2_monitor_t
/// @return     None
void r2u2_monitor_reset(r2u2_monitor_t* monitor);

#endif /* R2U2_MEMORY_MONITOR_H */
