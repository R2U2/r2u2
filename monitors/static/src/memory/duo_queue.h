#ifndef R2U2_MEMORY_DUOQ_H
#define R2U2_MEMORY_DUOQ_H

#include "internals/types.h"
#include "internals/errors.h"

/*
 *
 * Why we use time for so many things - fits because it's max you can meaningfully address
 * for example, we can safely do write_ptr +1 then modulo becase if it was going to overflow there woun't be room for the queue with control block
 *
 * Length, Size, and Capacity:
 * The length is the number of _____ required by the queue and is ...
 * The size is the number of queue slots ...
 * The capacity is the number of elements ...
 *
 */

#if R2U2_PRED_PROB
typedef struct {
  r2u2_tnt_t length;
  r2u2_tnt_t write;
  r2u2_tnt_t pred_write;
  r2u2_tnt_t read1;
  r2u2_tnt_t read2;
  r2u2_tnt_t next_time;
  r2u2_float prob;

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
     #error DUO Queues are only aligned for 32 or 64 bit pointer sizes
  #endif
  r2u2_tnt_t *queue;
} r2u2_duoq_control_block_t;
#else
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
     #error DUO Queues are only aligned for 32 or 64 bit pointer sizes
  #endif
  r2u2_tnt_t *queue;
} r2u2_duoq_control_block_t;
#endif

// Assumed to have same alignment as r2u2_tnt_t, that is can divide out sizeof
typedef struct {
    /* 64 or 32-bit platform:
     *   Size:     16 bytes
     *   Padding:   0 bytes
     *   Alignment: 4 bytes
     */
  r2u2_tnt_t lower_bound;
  r2u2_tnt_t upper_bound;
  r2u2_tnt_t edge;
  r2u2_tnt_t previous;
} r2u2_duoq_temporal_block_t;

#if R2U2_PRED_PROB
// Assumed to have same alignment as r2u2_tnt_t, that is can divide out sizeof
typedef struct {
    /* 64 or 32-bit platform:
     *   Size:     8 bytes
     *   Padding:   0 bytes
     *   Alignment: 2 bytes
     */
  r2u2_int deadline;
  r2u2_time k_modes;
} r2u2_duoq_predict_block_t;
#endif

typedef struct {
  r2u2_tnt_t start;
  r2u2_tnt_t end;
} r2u2_duoq_pt_interval_t;

/* DUO Queue Arena
 * Used by the monitor to track arena extents.
 * Since we access offsets from both ends of the arena, storing two pointers
 * instead of a pointer and a length is more useful. Also the different typing
 * of the two pointers makes it easier to avoid alignment change warnings.
 */
typedef struct {
  r2u2_duoq_control_block_t *blocks;
  r2u2_tnt_t *queues;
} r2u2_duoq_arena_t;

static inline r2u2_duoq_temporal_block_t* r2u2_duoq_ft_temporal_get(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  return (r2u2_duoq_temporal_block_t*)&((ctrl->queue)[ctrl->length]);
}

#if R2U2_PRED_PROB
static inline r2u2_duoq_predict_block_t* r2u2_duoq_ft_predict_get(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  // Checks to see if predict block even exists
  if (((arena->blocks)[queue_id-1].queue - ctrl->queue) < sizeof(r2u2_duoq_predict_block_t)/sizeof(r2u2_tnt_t)){
    return NULL;
  }
  else{
    return (r2u2_duoq_predict_block_t*)&((ctrl->queue)[ctrl->length]);
  }
}
#endif

/*
 *
 * Assumption: Queues are loaded in sequential order, i.e. when configuring
 * queue `n`, taking the queue pointer + lenght of queue `n-1` yields the ...
 */
r2u2_status_t r2u2_duoq_config(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_time queue_length, r2u2_time prob);

/*
 *
 *
 * Since this moves the queue poninter but reduces the length by the same step
 *
 * Checking for a temporal block by comparing the queue pointer against the
 * previous queue's pointer + length isn't guarenteed but should be sufficent.
 */
r2u2_status_t r2u2_duoq_ft_temporal_config(r2u2_duoq_arena_t *arena, r2u2_time queue_id);

#if R2U2_PRED_PROB
r2u2_status_t r2u2_duoq_ft_predict_config(r2u2_duoq_arena_t *arena, r2u2_time queue_id);
#endif

/* FT (SCQ replacement) */
r2u2_status_t r2u2_duoq_ft_write(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t value, r2u2_bool predict);
r2u2_bool r2u2_duoq_ft_check(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t *read, r2u2_tnt_t next_time, r2u2_tnt_t *value, r2u2_bool predict);

#if R2U2_PRED_PROB
r2u2_status_t r2u2_duoq_ft_write_probability(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_probability value, r2u2_bool predict);
r2u2_bool r2u2_duoq_ft_check_probability(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t *read, r2u2_tnt_t next_time, r2u2_probability *value, r2u2_bool predict);
#endif

/* PT (Box Queue replacement)
 * Control Block Values:
 *   - length:    Length
 *   - write:     Head
 *   - read1:     Tail
 *   - read2:     interval.end
 *   - next_time: interval.start
 *
 * R2U2_TNT_TRUE Used as empty value (previously R2U2_infin)
 */

static inline r2u2_time r2u2_duoq_pt_effective_id_get(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  return (r2u2_time)((ctrl->queue)[ctrl->length]);
}

r2u2_status_t r2u2_duoq_pt_effective_id_set(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_time effective_id);

static inline r2u2_status_t r2u2_duoq_pt_reset(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  ctrl->write = 0;
  ctrl->read1 = 0;
  return R2U2_OK;
}

static inline r2u2_bool r2u2_duoq_pt_is_empty(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  return ctrl->write == ctrl->read1;
}
static inline r2u2_bool r2u2_duoq_pt_is_full(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  return ((ctrl->write + 2) % ctrl->length) == ctrl->read1;
}

r2u2_status_t r2u2_duoq_pt_push(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_duoq_pt_interval_t value);

r2u2_duoq_pt_interval_t r2u2_duoq_pt_peek(r2u2_duoq_arena_t *arena, r2u2_time queue_id);
r2u2_duoq_pt_interval_t r2u2_duoq_pt_head_pop(r2u2_duoq_arena_t *arena, r2u2_time queue_id);
r2u2_duoq_pt_interval_t r2u2_duoq_pt_tail_pop(r2u2_duoq_arena_t *arena, r2u2_time queue_id);


#endif /* R2U2_MEMORY_DUOQ_H */
