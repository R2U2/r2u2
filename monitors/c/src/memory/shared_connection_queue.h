#ifndef R2U2_MEMORY_SCQ_H
#define R2U2_MEMORY_SCQ_H

#include "internals/types.h"
#include "internals/errors.h"

 typedef struct {
    /* 64 or 32-bit platform:
     *   Size:     16 bytes
     *   Padding:   0 bytes
     *   Alignment: 4 bytes
     */
  r2u2_tnt_t edge;
  r2u2_tnt_t previous;
  r2u2_time lower_bound;
  r2u2_time upper_bound;
} r2u2_scq_temporal_block_t;

typedef struct {
  r2u2_tnt_t length;
  r2u2_tnt_t write;
  r2u2_tnt_t read1;
  r2u2_tnt_t read2;
  r2u2_tnt_t next_time;
  /*
   *
   * Portable, architecture-agnostic pointer size detection from:
   * https://stackoverflow.com/a/61017823
   */
  #if INTPTR_MAX == INT64_MAX
    /* 64-bit Platform
     *   Size:     32 bytes
     *   Padding:   4 bytes
     *   Alignment: 8 bytes
     */
    uint8_t _pad[4];
  #elif INTPTR_MAX == INT32_MAX
    /* 32-bit Platform
     *   Size:     28 bytes
     *   Padding:   0 bytes
     *   Alignment: 4 bytes
     */
  #else
     #error Shared Connection Queues are only aligned for 32 or 64 bit pointer sizes
  #endif
  r2u2_scq_temporal_block_t temporal_block;
  r2u2_tnt_t *queue;
} r2u2_scq_control_block_t;

/* Shared Connection Queue Arena
 * Used by the monitor to track arena extents.
 * Since we access offsets from both ends of the arena, storing two pointers
 * instead of a pointer and a length is more useful. Also the different typing
 * of the two pointers makes it easier to avoid alignment change warnings.
 */
typedef struct {
  r2u2_scq_control_block_t *blocks;
  r2u2_tnt_t *queues;
} r2u2_scq_arena_t;

/*
 *
 * Assumption: Queues are loaded in sequential order, i.e. when configuring
 * queue `n`, taking the queue pointer + lenght of queue `n-1` yields the ...
 */
r2u2_status_t r2u2_scq_config(r2u2_scq_arena_t arena, r2u2_time queue_id, r2u2_time queue_length);

/* SCQ Read and Write */
r2u2_status_t r2u2_scq_write(r2u2_scq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t value);
r2u2_bool r2u2_scq_check(r2u2_scq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t *read, r2u2_tnt_t next_time, r2u2_tnt_t *value);

#endif /* R2U2_MEMORY_SCQ_H */
