#include "r2u2.h"

#include "duo_queue.h"

#if R2U2_DEBUG
static void r2u2_duoq_arena_print(r2u2_duoq_arena_t *arena) {
  R2U2_DEBUG_PRINT("\t\t\tDUO Queue Arena:\n\t\t\t\tBlocks: <%p>\n\t\t\t\tQueues: <%p>\n\t\t\t\tSize: %ld\n", arena->blocks, arena->queues, ((void*)arena->queues) - ((void*)arena->blocks));
}

static void r2u2_duoq_queue_print(r2u2_duoq_arena_t *arena, r2u2_time queue_id) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_PRED_PROB
    R2U2_DEBUG_PRINT("\t\t\tID: |");
    for (r2u2_time i = 0; i < ctrl->length; ++i) {
      R2U2_DEBUG_PRINT(" <%p> |", (void*)&((ctrl->queue)[i]));
    }
    R2U2_DEBUG_PRINT("\n\t\t\t%3d |", queue_id);
    for (r2u2_time i = 0; i < ctrl->length; ++i) {
      if(ctrl->prob > 1.0){ //Indicates Probabilistic operator
        r2u2_probability value = (*(r2u2_probability*)&((ctrl->queue)[(i) * (sizeof(r2u2_probability)/sizeof(r2u2_tnt_t))]));
        R2U2_DEBUG_PRINT("  %0.4f:%4d  |", value.prob, value.time);
      } 
      else {
        R2U2_DEBUG_PRINT("  %s:%9d  |", ((ctrl->queue)[i] & R2U2_TNT_TRUE) ? "T" : "F", ((ctrl->queue)[i] & R2U2_TNT_TIME));
      }
    }
    R2U2_DEBUG_PRINT("\n");
  #else
    R2U2_DEBUG_PRINT("\t\t\tID: |");
    for (r2u2_time i = 0; i < ctrl->length; ++i) {
      R2U2_DEBUG_PRINT(" <%p> |", (void*)&((ctrl->queue)[i]));
    }
    R2U2_DEBUG_PRINT("\n\t\t\t%3d |", queue_id);
    for (r2u2_time i = 0; i < ctrl->length; ++i) {
      R2U2_DEBUG_PRINT("  %s:%9d  |", ((ctrl->queue)[i] & R2U2_TNT_TRUE) ? "T" : "F", ((ctrl->queue)[i] & R2U2_TNT_TIME));
    }
    R2U2_DEBUG_PRINT("\n");
  #endif
  // R2U2_DEBUG_PRINT("\t\t\t%*cW\n", (int)(((6 * ctrl->length)-3)-(6 * (ctrl->write))), ' ');
  // R2U2_DEBUG_PRINT("\t\t\t%*cW_p\n", (int)(((6 * ctrl->length)-3)-(6 * (ctrl->pred_write))), ' ');
}
#endif

r2u2_status_t r2u2_duoq_config(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_time queue_length, r2u2_time prob) {

  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_PRED_PROB
    ctrl->pred_write = r2u2_infinity;
    ctrl->prob = prob / 1000000.0;
    if (ctrl->prob == 3.0){ // Temporal Probabilistic Operator
      int reserved_for_temp_block = sizeof(r2u2_duoq_temporal_block_t) / sizeof(r2u2_tnt_t);
      ctrl->length = (sizeof(r2u2_probability)/sizeof(r2u2_tnt_t))*(queue_length - reserved_for_temp_block) + reserved_for_temp_block;
    }
    else if(ctrl->prob == 2.0){ // Probabilistic Operator
      ctrl->length = (sizeof(r2u2_probability)/sizeof(r2u2_tnt_t))*queue_length;
    }
    else{
      ctrl->length = queue_length;
    }
  #else
    ctrl->length = queue_length;
  #endif

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

  ctrl->queue[0] = r2u2_infinity;

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

#if R2U2_PRED_PROB
r2u2_status_t r2u2_duoq_ft_predict_config(r2u2_duoq_arena_t *arena, r2u2_time queue_id){
    
  #if R2U2_DEBUG
    assert((arena->blocks)[queue_id].length > sizeof(r2u2_duoq_predict_block_t) / sizeof(r2u2_tnt_t));
  #endif

  // Reserve predict block by shortening length of circular buffer
  (arena->blocks)[queue_id].length -= sizeof(r2u2_duoq_predict_block_t) / sizeof(r2u2_tnt_t);

  R2U2_DEBUG_PRINT("\t\tCfg DUOQ %u: Predict Rsvd, len = %u\n", queue_id, (arena->blocks)[queue_id].length);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  return R2U2_OK;
}
#endif

#if R2U2_PRED_PROB
r2u2_status_t r2u2_duoq_ft_write(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t value, r2u2_bool predict) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);
  r2u2_tnt_t *temp_write;
  if (predict){
    temp_write = &ctrl->pred_write;
  }
  else{
    temp_write = &ctrl->write;
  }

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif


  r2u2_tnt_t prev = ((*temp_write) == 0) ? ctrl->length-1 : *temp_write-1;

  // Three checks:
  //    1: Is the new verdict the same as the previous? i.e. truth bit is clear
  //       in an xor and therefore the value is less than max time
  //    2: Coherence, if the previous timestamp matches the one under the write
  //       pointer, either this is the first write or we're in an incoherent
  //       state, write to the next cell instead.
  //    3: Is the previous data real data? If so, don't overwrite with compact writing.
  if ((((ctrl->queue)[prev] ^ value) <= R2U2_TNT_TIME) && \
      ((ctrl->queue)[prev] != (ctrl->queue)[*temp_write]) && \
      (ctrl->write != ctrl->pred_write) && \
      (ctrl->queue)[ctrl->write] != r2u2_infinity) {
    R2U2_DEBUG_PRINT("\t\tCompacting write\n");
    *temp_write = prev;
  }
  // Here the write offset is ready in all cases, write and advance
  (ctrl->queue)[*temp_write] = value;

  if(predict){ 
    // Ensure that predicted data never overwrites real relevant data
    *temp_write = (((*temp_write + 1) % ctrl->length) == ((ctrl->write + ((ctrl->length-1)/2)+1) % ctrl->length)) ? *temp_write = ctrl->write : ((*temp_write + 1) % ctrl->length);
  }else{
    // Yes, in the compacted case we're redoing what we undid, but ...
    *temp_write = (*temp_write + 1) % ctrl->length;
  }

  // When overwriting predicted data with real data reset pred_write
  if(!predict && ctrl->write == ctrl->pred_write){
    ctrl->pred_write = r2u2_infinity;
  }

  R2U2_DEBUG_PRINT("\t\tNew Write Ptr: %u\n", *temp_write);

  return R2U2_OK;
}
r2u2_status_t r2u2_duoq_ft_write_probability(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_probability value, r2u2_bool predict) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  r2u2_tnt_t *temp_write;
  if (predict){
    temp_write = &ctrl->pred_write;
  }
  else{
    temp_write = &ctrl->write;
  }

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  // Standard write of r2u2_probability value to queue
  r2u2_probability* prob_slot = (r2u2_probability*)&((ctrl->queue)[(*temp_write) * (sizeof(r2u2_probability)/sizeof(r2u2_tnt_t))]);
  *prob_slot = value;

  if(predict){ 
    // Ensure that predicted data never overwrites real relevant data
    *temp_write = (((*temp_write + 1) % ctrl->length) == ((ctrl->write + ((ctrl->length-1)/2)+1) % ctrl->length)) ? *temp_write = ctrl->write : ((*temp_write + 1) % ctrl->length);
  }else{
    // Increment write pointer
    *temp_write = (*temp_write + 1) % ctrl->length;
  }

  // When overwriting predicted data with real data reset pred_write
  if(!predict && ctrl->write == ctrl->pred_write){
    ctrl->pred_write = r2u2_infinity;
  }

  R2U2_DEBUG_PRINT("\t\tNew Write Ptr: %u\n", *temp_write);

  return R2U2_OK;
}
#else
r2u2_status_t r2u2_duoq_ft_write(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t value) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif


  r2u2_tnt_t prev = ((ctrl->write) == 0) ? ctrl->length-1 : ctrl->write-1;

  // Three checks:
  //    1: Is the new verdict the same as the previous? i.e. truth bit is clear
  //       in an xor and therefore the value is less than max time
  //    2: Coherence, if the previous timestamp matches the one under the write
  //       pointer, either this is the first write or we're in an incoherent
  //       state, write to the next cell instead.
  if ((((ctrl->queue)[prev] ^ value) <= R2U2_TNT_TIME) && \
      ((ctrl->queue)[prev] != (ctrl->queue)[ctrl->write]) && \
      (ctrl->queue)[ctrl->write] != r2u2_infinity) {
    R2U2_DEBUG_PRINT("\t\tCompacting write\n");
    ctrl->write = prev;
  }
  // Here the write offset is ready in all cases, write and advance
  (ctrl->queue)[ctrl->write] = value;

  // Yes, in the compacted case we're redoing what we undid, but ...
  ctrl->write = (ctrl->write + 1) % ctrl->length;

  R2U2_DEBUG_PRINT("\t\tNew Write Ptr: %u\n", *temp_write);

  return R2U2_OK;
}
#endif

#if R2U2_PRED_PROB
r2u2_bool r2u2_duoq_ft_check(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t *read, r2u2_tnt_t next_time, r2u2_tnt_t *value, r2u2_bool predict) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  // Checks if trying to read predicted data when not in predictive mode
  if(!predict && *read == ctrl->pred_write){
    R2U2_DEBUG_PRINT("\t\tRead Ptr %u == Prediction Write Ptr %u\n", *read, ctrl->pred_write);
    return false; 
  }

  r2u2_tnt_t *temp_write;
  if (predict){
    temp_write = &ctrl->pred_write;
    R2U2_DEBUG_PRINT("\t\t\tRead: %u\n\t\t\tTime: %u,\n\t\t\tPrediction Write: %u\n", *read, next_time, *temp_write);
  }
  else{
    temp_write = &ctrl->write;
    R2U2_DEBUG_PRINT("\t\t\tRead: %u\n\t\t\tTime: %u,\n\t\t\tWrite: %u\n", *read, next_time, *temp_write);
  }

  do {
    // Check if time pointed to is >= desired time by discarding truth bits
    if (((ctrl->queue)[*read] & R2U2_TNT_TIME) >= next_time && ((ctrl->queue)[*read] != r2u2_infinity)) {
      // Return value
      R2U2_DEBUG_PRINT("New data found after scanning t=%d\n", (ctrl->queue)[*read] & R2U2_TNT_TIME);
      *value = (ctrl->queue)[*read];
      return true;
    }
    // Current slot is too old, step forword to check for new data
    *read = (*read + 1) % ctrl->length;
  } while (*read != *temp_write);

  // Here we hit the write pointer while scanning forwards, take a step back
  // in case the next value is compacted onto the slot we just checked.
  *read = (*read == 0) ? ctrl->length-1 : *read-1;

  // Queue is empty
  R2U2_DEBUG_PRINT("\t\tNo new data Read Ptr %u and Write Ptr %u and t=%d\n", *read, ctrl->write, next_time);
  return false;
}
r2u2_bool r2u2_duoq_ft_check_probability(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t *read, r2u2_tnt_t next_time, r2u2_probability *value, r2u2_bool predict) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  R2U2_DEBUG_PRINT("\t\t\tRead: %u\n\t\t\tTime: %u\n", *read, next_time);

  // Checks if trying to read predicted data when not in predictive mode
  if(!predict && *read == ctrl->pred_write){
    R2U2_DEBUG_PRINT("\t\tNot predicting and Read Ptr %u == Prediction Write Ptr %u\n", *read, ctrl->pred_write);
    return false; 
  }

  r2u2_tnt_t *temp_write;
  if (predict){
    temp_write = &ctrl->pred_write;
  }
  else{
    temp_write = &ctrl->write;
  }

  if (*read == *temp_write) {
    *value = (*(r2u2_probability*)&((ctrl->queue)[(*read) * (sizeof(r2u2_probability)/sizeof(r2u2_tnt_t))]));
    if (value->time >= next_time && *temp_write != r2u2_infinity && ((ctrl->queue)[*read] != r2u2_infinity)){
      // Return value
      R2U2_DEBUG_PRINT("\t\tNew data found in place t=%d >= %d\n", value->time, next_time);
      return true;
    }
    // Queue is empty
    R2U2_DEBUG_PRINT("\t\tEmpty Queue Read Ptr %u == Write Ptr %u and t=%d\n", *read, ctrl->write, next_time);
    return false;
  }


  do {
    // Check if time pointed to is >= desired time by discarding truth bits
    *value = (*(r2u2_probability*)&((ctrl->queue)[(*read) * (sizeof(r2u2_probability)/sizeof(r2u2_tnt_t))]));
    if (value->time >= next_time) {
      // Return value
      R2U2_DEBUG_PRINT("New data found after scanning t=%d\n", value->time);
      return true;
    }
    // Current slot is too old, step forword to check for new data
    *read = (*read + 1) % ctrl->length;
  } while (*read != *temp_write);

  // Here we hit the write pointer while scanning forwards, take a step back
  // in case the next value is compacted onto the slot we just checked.
  *read = (*read == 0) ? ctrl->length-1 : *read-1;
  return false;
}
#else
r2u2_bool r2u2_duoq_ft_check(r2u2_duoq_arena_t *arena, r2u2_time queue_id, r2u2_tnt_t *read, r2u2_tnt_t next_time, r2u2_tnt_t *value) {
  r2u2_duoq_control_block_t *ctrl = &((arena->blocks)[queue_id]);

  #if R2U2_DEBUG
  r2u2_duoq_queue_print(arena, queue_id);
  #endif

  R2U2_DEBUG_PRINT("\t\t\tRead: %u\n\t\t\tTime: %u,\n\t\t\tWrite: %u\n", *read, next_time, ctrl->write);

  do {
    // Check if time pointed to is >= desired time by discarding truth bits
    if (((ctrl->queue)[*read] & R2U2_TNT_TIME) >= next_time && ((ctrl->queue)[*read] != r2u2_infinity)) {
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

  // Queue is empty
  R2U2_DEBUG_PRINT("\t\tNo new data Read Ptr %u and Write Ptr %u and t=%d\n", *read, ctrl->write, next_time);
  return false;
}
#endif

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
