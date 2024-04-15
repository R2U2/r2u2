#include "r2u2.h"

#include "duo_queue.h"

#if R2U2_DEBUG
static void r2u2_duoq_arena_print(r2u2_duoq_arena_t *arena) {
  R2U2_DEBUG_PRINT("\t\t\tDUO Queue Arena:\n\t\t\t\tBlocks: <%p>\n\t\t\t\tQueues: <%p>\n\t\t\t\tSize: %d\n", arena->blocks, arena->queues, ((void*)arena->queues) - ((void*)arena->blocks));
}

static void r2u2_duoq_queue_print(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  R2U2_DEBUG_PRINT("\t\t\tID: |");
  for (r2u2_time i = 0; i < ctrl->length; ++i) {
    R2U2_DEBUG_PRINT(" <%p> |", (void*)&((ctrl->queue)[i]));
  }
  R2U2_DEBUG_PRINT("\n\t\t\t%3d |", queue_id);
  for (r2u2_time i = 0; i < ctrl->length; ++i) {
    R2U2_DEBUG_PRINT("  %s:%9d  |", ((ctrl->queue)[i] & R2U2_TNT_TRUE) ? "T" : "F", ((ctrl->queue)[i] & R2U2_TNT_TIME));
  }
  R2U2_DEBUG_PRINT("\n");
}
#endif

r2u2_status_t r2u2_duoq_config(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_time queue_length) {

  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  ctrl->length = queue_length;

  R2U2_DEBUG_PRINT("\t\tCfg DUOQ %u: len = %u\n", queue_id, queue_length);

  /* The first queue doesn't have a previous queue to offset from and can use
   * the slot pointed to by the control block queue pointer, so if the queue id
   * is zero, we use a different offset calculation.
   */
  if (r2u2_unlikely(queue_id == 0)) {
    // First queue counts back from end of arena, inclusive
    ctrl->queue = arena->queues - (queue_length - 1);
  } else {
    // All subsuquent queues count back from previous queue, exclusive
    ctrl->queue = (arena->blocks)[queue_id-1].queue - queue_length;
  }

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  return R2U2_OK;
}

r2u2_status_t r2u2_duoq_ft_temporal_config(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {

  #if R2U2_DEBUG
    assert((arena->blocks)[queue_id].length > sizeof(r2u2_duoq_temporal_block_t) / sizeof(r2u2_tnt_t));
  #endif

  // Reserve temporal block by shortening length of circular buffer
  (arena->blocks)[queue_id].length -= sizeof(r2u2_duoq_temporal_block_t) / sizeof(r2u2_tnt_t);

  R2U2_DEBUG_PRINT("\t\tCfg DUOQ %u: Temp Rsvd, len = %u\n", queue_id, (arena->blocks)[queue_id].length);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  return R2U2_OK;
}

r2u2_status_t r2u2_duoq_ft_write(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t value) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  /* We don't check for compaction on first write, so we discard the truth bit
   * (tnt << 1) and check for time == 0 (technically 2 * time == 0) and only
   * check for compaction if that fails.
   */
  // TODO(bckempa): There a tons of ways to structure this conditional flow,
  // but figuring out which is best would depend too much on the target and
  // compiler to slect, so just stick with something readable

  // Compation check -

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  // TODO(bckempa): Which is faster? Probably the modulo if it's safe...
  // r2u2_tnt_t prev = (ctrl->write == 0) ? ctrl->length-1 : ctrl->write-1;
  r2u2_tnt_t prev = (ctrl->write-1) % ctrl->length;
  // Two checks:
  //    1: Is the new verdict the same as the previous? i.e. truth bit is clear
  //       in an xor and therefore the value is less than max time
  //    2: Coherence, if the previous timestamp matches the one under the write
  //       pointer, either this is the first write or we're in an incoherent
  //       state, write to the next cell instead.
  if ((((ctrl->queue)[prev] ^ value) <= R2U2_TNT_TIME) && \
      ((ctrl->queue)[prev] != (ctrl->queue)[ctrl->write])) {
    R2U2_DEBUG_PRINT("\t\tCompating write\n");
    ctrl->write = prev;
  }

  // Here the write offset is ready in all cases, write and advance
  (ctrl->queue)[ctrl->write] = value;
  // Yes, in the compacted case we're redoing what we undid, but ...
  ctrl->write = (ctrl->write + 1) % ctrl->length;

  R2U2_DEBUG_PRINT("\t\tNew Write Ptr: %u\n", ctrl->write);

  return R2U2_OK;
}

r2u2_bool r2u2_duoq_ft_check(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t *read, r2u2_tnt_t next_time, r2u2_tnt_t *value) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  R2U2_DEBUG_PRINT("\t\t\tRead: %u\n\t\t\tTime: %u\n", *read, next_time);

  if (*read == ctrl->write) {
    // Queue is empty
    R2U2_DEBUG_PRINT("\t\tRead Ptr %u == Write Ptr %u\n", *read, ctrl->write);
    return false;
  }


  do {
    // Check if time pointed to is >= desired time by discarding truth bits
    if (((ctrl->queue)[*read] << 1) >= (next_time << 1)) {
      // Return value
      *value = (ctrl->queue)[*read];
      return true;
    }
    // Current slot is too old, step forword to check for new data
    *read = (*read+1) % ctrl->length;
  } while (*read != ctrl->write);

  // Here we hit the write pointer while scanning forwords, take a step back
  // in case the next value is compacted onto the slot we just checked.
  *read = (*read-1) % ctrl->length;
  return false;
}

r2u2_status_t r2u2_duoq_pt_effective_id_set(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_time effective_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_DEBUG
    assert(ctrl->length > sizeof(r2u2_time) / sizeof(r2u2_tnt_t));
  #endif

  // Reserve temporal block by shortening length of circular buffer
  ctrl->length -= sizeof(r2u2_time) / sizeof(r2u2_tnt_t);

  ((ctrl->queue)[ctrl->length]) = effective_id;

  R2U2_DEBUG_PRINT("\t\tCfg DUOQ %u: EID Set %u, len = %u\n", queue_id, ((ctrl->queue)[ctrl->length]), (arena->blocks)[queue_id].length);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  return R2U2_OK;
}

r2u2_status_t r2u2_duoq_pt_push(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_duoq_pt_interval_t value) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_DEBUG
    R2U2_DEBUG_PRINT("PT Queue %d len %d\n", queue_id, ctrl->length);
    if (r2u2_duoq_pt_is_full(arena, queue_id)) {
      R2U2_DEBUG_PRINT("WARNING: PT Queue Overflow\n");
    }
  #endif

  (ctrl->queue)[ctrl->write] = value.start;
  (ctrl->queue)[ctrl->write + 1] = value.end;

  ctrl->write = (ctrl->write == ctrl->length-2) ? 0 : ctrl->write + 2;

  return R2U2_OK;
}

r2u2_duoq_pt_interval_t r2u2_duoq_pt_peek(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  if (r2u2_duoq_pt_is_empty(arena, queue_id)) {
    return (r2u2_duoq_pt_interval_t){R2U2_TNT_TRUE, R2U2_TNT_TRUE};
  } else {
    return (r2u2_duoq_pt_interval_t){(ctrl->queue)[ctrl->read1], (ctrl->queue)[ctrl->read1 + 1]};
  }
}

r2u2_duoq_pt_interval_t r2u2_duoq_pt_head_pop(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

    if (r2u2_duoq_pt_is_empty(arena, queue_id)) {
      R2U2_DEBUG_PRINT("WARNING: PT Head Underflow\n");
      return (r2u2_duoq_pt_interval_t){R2U2_TNT_TRUE, R2U2_TNT_TRUE};
    } else {
      // Write head always points at invalid data, so we decrement before read
      ctrl->write = (ctrl->write == 0) ? ctrl->length-2 : ctrl->write - 2;
      return (r2u2_duoq_pt_interval_t){(ctrl->queue)[ctrl->write], (ctrl->queue)[ctrl->write + 1]};
    }
}

r2u2_duoq_pt_interval_t r2u2_duoq_pt_tail_pop(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  r2u2_tnt_t result_index;

    if (r2u2_duoq_pt_is_empty(arena, queue_id)) {
      R2U2_DEBUG_PRINT("WARNING: PT Tail Underflow\n");
      return (r2u2_duoq_pt_interval_t){R2U2_TNT_TRUE, R2U2_TNT_TRUE};
    } else {
      result_index = ctrl->read1;
      ctrl->read1 = (ctrl->read1 == ctrl->length-2) ? 0 : ctrl->read1 + 2;
      return (r2u2_duoq_pt_interval_t){(ctrl->queue)[result_index], (ctrl->queue)[result_index + 1]};
    }
}
