#include "shared_connection_queue.h"
#include "internals/debug.h"

r2u2_status_t r2u2_scq_write(r2u2_scq_arena_t arena, r2u2_time queue_id, r2u2_tnt_t value) {
  r2u2_scq_control_block_t *ctrl = &((arena.blocks)[queue_id]);

  #if R2U2_DEBUG
  r2u2_scq_queue_print(arena, queue_id);
  #endif

  r2u2_addr prev = ((ctrl->write) == 0) ? ctrl->length-1 : ctrl->write-1;

  // Three checks:
  //    1: Is the new verdict the same as the previous? i.e. truth bit is clear
  //       in an xor and therefore the value is less than max time
  //    2: Coherence, if the previous timestamp matches the one under the write
  //       pointer, either this is the first write or we're in an incoherent
  //       state, write to the next cell instead.
  //.   3: Cell is not empty, i.e., not `r2u2_infinity`
  if ((((ctrl->queue)[prev] ^ value) <= R2U2_TNT_TIME) && \
      ((ctrl->queue)[prev] != (ctrl->queue)[ctrl->write]) && \
      ((ctrl->queue)[ctrl->write] != r2u2_infinity)) {
    R2U2_DEBUG_PRINT("\t\tCompacting write\n");
    ctrl->write = prev;
  }

  // Here the write offset is ready in all cases, write and advance
  (ctrl->queue)[ctrl->write] = value;
  // Yes, in the compacted case we're redoing what we undid, but ...
  ctrl->write = (ctrl->write + 1) % ctrl->length;

  R2U2_DEBUG_PRINT("\t\tNew Write Ptr: %u\n", ctrl->write);

  return R2U2_OK;
}

r2u2_bool r2u2_scq_read(r2u2_scq_arena_t arena, r2u2_time queue_id, r2u2_addr *read, r2u2_addr next_time, r2u2_tnt_t *value) {
  r2u2_scq_control_block_t *ctrl = &((arena.blocks)[queue_id]);

  #if R2U2_DEBUG
  r2u2_scq_queue_print(arena, queue_id);
  #endif

  R2U2_DEBUG_PRINT("\t\t\tRead: %u\n\t\t\tTime: %u,\n\t\t\tWrite: %u\n", *read, next_time, ctrl->write);

  if ((ctrl->queue)[*read] == r2u2_infinity){
      //Empty Queue
      R2U2_DEBUG_PRINT("\t\tEmpty Queue\n");
      return false;
  }

  do {
    // Check if time pointed to is >= desired time by discarding truth bits
    if (((ctrl->queue)[*read] & R2U2_TNT_TIME) >= next_time) {
      // Return value
      R2U2_DEBUG_PRINT("New data found after scanning t=%d\n", (ctrl->queue)[*read] & R2U2_TNT_TIME);
      *value = (ctrl->queue)[*read];
      return true;
    }
    // Current slot is too old, step forword to check for new data
    *read = (*read + 1) % ctrl->length;
  } while (*read != ctrl->write);

  // Here we hit the write pointer while scanning forwards, take a step back
  // in case the next value is compacted onto the slot we just checked.
  *read = (*read == 0) ? ctrl->length-1 : *read-1;

  // No new data in queue
  R2U2_DEBUG_PRINT("\t\tNo new data Read Ptr %u and Write Ptr %u and t=%d\n", *read, ctrl->write, next_time);
  return false;
}