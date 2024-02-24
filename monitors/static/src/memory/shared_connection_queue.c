#include "r2u2.h"

#include "shared_connection_queue.h"

// TODO(bckempa): Currently, we use infinity (defined as the maximum value of
//                r2u2_time) to initialize the queue. Instead of adding extra
//                checks, it might be more efficent, but slightly less readable
//                to use 0 as the sentinal value and store all timestamps as
//                t+1 to differentiate t=0 from no data.

// NOTE: Since the SCQ circular buffers grow backwards from the end of the
//       arena, all indicies should be negative offsets from the queue pointer
//       but are stored as positve integers to be read easier

#if R2U2_DEBUG
static void r2u2_scq_print(r2u2_scq_t *scq, r2u2_time *rd_ptr) {

  if (rd_ptr != NULL) {
    R2U2_DEBUG_PRINT("\t\t\t%*cR\n", (int)(((6 * (ptrdiff_t)scq->length)-3)-(6 * (*rd_ptr))), ' ');
  }

  R2U2_DEBUG_PRINT("\t\t\t|");
  for (unsigned int i = 0; i < scq->length; ++i) {
    R2U2_DEBUG_PRINT(" %03d |", (scq->queue)[(1 - (ptrdiff_t)scq->length) + i].time);
  }
  R2U2_DEBUG_PRINT("\n\t\t\t|");
  for (unsigned int i = 0; i < scq->length; ++i) {
    R2U2_DEBUG_PRINT("  %1d  |", (scq->queue)[(1 - (ptrdiff_t)scq->length) + i].truth);
  }
  R2U2_DEBUG_PRINT(" <%p>\n", (void*)scq->queue);
  R2U2_DEBUG_PRINT("\t\t\t%*cW\n", (int)(((6 * (ptrdiff_t)scq->length)-3)-(6 * (scq->wr_ptr))), ' ');
}
#endif

r2u2_status_t r2u2_scq_push(r2u2_scq_t *scq, r2u2_verdict *res, r2u2_time *wr_ptr) {
  R2U2_DEBUG_PRINT("\t\tPushing to SCQ <%p> Length: (%d)\n", (void*)scq->queue, scq->length);
  R2U2_DEBUG_PRINT("\t\tWrite Pointer Pre: [%d]<%p> -> (%d, %d, %f)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth, (scq->queue)[-((ptrdiff_t)*wr_ptr)].prob);
  #if R2U2_DEBUG
  r2u2_scq_print(scq, NULL);
  #endif

  // When overwriting predicted data with real data reset pred_wr_ptr
  if(wr_ptr == &scq->wr_ptr && *wr_ptr == scq->pred_wr_ptr){
    scq->pred_wr_ptr = r2u2_infinity;
  }

  // TODO(bckempa): Verify compiler removes redundant modulo arith, else inline
  if ((scq->queue)[-((ptrdiff_t)*wr_ptr)].time == r2u2_infinity) {
    // Initialization behavior
    R2U2_DEBUG_PRINT("\t\tInitial Write\n");
    (scq->queue)[-((ptrdiff_t)*wr_ptr)] = *res;
    *wr_ptr = (*wr_ptr + 1) % scq->length;
    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d, %f)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth,  (scq->queue)[-((ptrdiff_t)*wr_ptr)].prob);
    #if R2U2_DEBUG
    r2u2_scq_print(scq, NULL);
    #endif
    return R2U2_OK;
  }
  if (((scq->queue)[-((ptrdiff_t)((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1))].truth == res->truth) && \
      ((scq->queue)[-((ptrdiff_t)((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1))].time < res->time) && \
      (scq->wr_ptr != scq->pred_wr_ptr)) {
    R2U2_DEBUG_PRINT("\t\tAggregate Write\n");
    // Aggregate write, overwrite the previous cell to update timestamp
    (scq->queue)[-((ptrdiff_t)((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1))] = *res;

    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth);
    #if R2U2_DEBUG
    r2u2_scq_print(scq, NULL);
    #endif
    return R2U2_OK;
  } else {
    // Standard write
    R2U2_DEBUG_PRINT("\t\tStandard Write\n");
    (scq->queue)[-((ptrdiff_t)*wr_ptr)] = *res;
    if(wr_ptr == &scq->pred_wr_ptr){ // Ensure that predicted data never overwrites real relevant data
      *wr_ptr = (((*wr_ptr + 1) % scq->length) == ((scq->wr_ptr + ((scq->length-1)/2)+1) % scq->length)) ? *wr_ptr = scq->wr_ptr : ((*wr_ptr + 1) % scq->length);
    }else{
      *wr_ptr = (*wr_ptr + 1) % scq->length;
    }
    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d, %f)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth, (scq->queue)[-((ptrdiff_t)*wr_ptr)].prob);
    #if R2U2_DEBUG
    r2u2_scq_print(scq, NULL);
    #endif
    return R2U2_OK;
  }
  return R2U2_ERR_OTHER;
}

r2u2_verdict r2u2_scq_pop(r2u2_scq_t *scq, r2u2_time *rd_ptr) {
  // TODO(bckempa): This is a misnomer, it's a peek not a pop

  // This is an obvious inlining candidate
  return (scq->queue)[-((ptrdiff_t)*rd_ptr)];
}

// TODO(bckempa): Maybe it makes sense to pair the read pointers and desired times?
//                Need to verify algotihmic implication, though may reduce redundent data
r2u2_bool r2u2_scq_is_empty(r2u2_scq_t *scq, r2u2_time *rd_ptr, r2u2_time *desired_time_stamp, bool predict) {
  R2U2_DEBUG_PRINT("\t\tSCQ before finding read:\n");
  // NOTE: This should be the child SCQ, but the parent's read ptr
  // this ensureds CSE works by allowing many readers

  r2u2_time *wr_ptr;
  if(predict){
    wr_ptr = &scq->pred_wr_ptr;
  }else{
    wr_ptr = &scq->wr_ptr;
  }

  R2U2_DEBUG_PRINT("\t\tSCQ Empty Check\n");
  R2U2_DEBUG_PRINT("\t\tRead Pointer Pre: [%d]<%p> -> (%d, %d, %f)\n", *rd_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*rd_ptr)]), (scq->queue)[-((ptrdiff_t)*rd_ptr)].time, (scq->queue)[-((ptrdiff_t)*rd_ptr)].truth, (scq->queue)[-((ptrdiff_t)*rd_ptr)].prob);
  #if R2U2_DEBUG
  r2u2_scq_print(scq, rd_ptr);
  #endif

  // Checks if trying to read predicted data when not in predictice mode
  if(!predict && *rd_ptr == scq->pred_wr_ptr){
    return true; 
  }

  if ((scq->queue)[-((ptrdiff_t)*rd_ptr)].time >= *desired_time_stamp && (scq->queue)[-((ptrdiff_t)*rd_ptr)].time != r2u2_infinity) {
    // New data available
    R2U2_DEBUG_PRINT("\t\tNew data found in place t=%d >= %d\n", (scq->queue)[-((ptrdiff_t)*rd_ptr)].time, *desired_time_stamp);
    return false;
  } else if (*rd_ptr != ((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1)) {

    // Fast-forword queue
    while ((*rd_ptr != ((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1)) && ((scq->queue)[-((ptrdiff_t)*rd_ptr)].time < *desired_time_stamp)) {
      R2U2_DEBUG_PRINT("\t\tScanning queue t=%d < %d\n", (scq->queue)[-((ptrdiff_t)*rd_ptr)].time, *desired_time_stamp);
      *rd_ptr = (*rd_ptr + 1) % scq->length;
      #if R2U2_DEBUG
      r2u2_scq_print(scq, rd_ptr);
      #endif
    }

    if ((scq->queue)[-((ptrdiff_t)*rd_ptr)].time < *desired_time_stamp) {
      // Ternary conditional handles pointer decriment modulo SCQ length without casting to and back from signed integers
      *rd_ptr = (*rd_ptr == 0) ? scq->length-1 : *rd_ptr-1;
      R2U2_DEBUG_PRINT("\t\tNo new data found after scanning t=%d\n", (scq->queue)[-((ptrdiff_t)*rd_ptr)].time);
      #if R2U2_DEBUG
      r2u2_scq_print(scq, rd_ptr);
      #endif
      return true;
    } else {
      R2U2_DEBUG_PRINT("\t\tNew data found after scanning t=%d\n", (scq->queue)[-((ptrdiff_t)*rd_ptr)].time);
      return false;
    }
  } else { // Empty queue - read == write ptr, current value stale
    R2U2_DEBUG_PRINT("\t\tEmpty Queue Rd == Wrt and t=%d < %d\n", (scq->queue)[-((ptrdiff_t)*rd_ptr)].time, *desired_time_stamp);
    return true;
  }

  return R2U2_OK;
}
