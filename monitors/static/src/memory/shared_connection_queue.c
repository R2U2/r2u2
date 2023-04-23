#include "r2u2.h"

#include "shared_connection_queue.h"

// NOTE: Since the SCQ circular buffers grow backwards from the end of the
//       arena, all indicies should be negative offsets from the queue pointer
//       but are stored as positve integers to be read easier

r2u2_status_t r2u2_scq_push(r2u2_scq_t *scq, r2u2_verdict *res) {
  R2U2_DEBUG_PRINT("\t\tPushing to SCQ <%p> Lenght: (%d)\n", scq->queue, scq->length);
  R2U2_DEBUG_PRINT("\t\tWrite Pointer Pre: [%d]<%p> -> (%d, %d)\n", scq->wr_ptr, &((scq->queue)[-(scq->wr_ptr)]), (scq->queue)[-(scq->wr_ptr)].time, (scq->queue)[-(scq->wr_ptr)].truth);

  // TODO(bckempa): Verify compiler removes redundant modulo arith, else inline
  if ((scq->queue)[-(scq->wr_ptr)].time == r2u2_infinity) {
    // Initialization behavior
    R2U2_DEBUG_PRINT("\t\tInitial Write\n");
    (scq->queue)[-(scq->wr_ptr)] = *res;
    scq->wr_ptr = (scq->wr_ptr + 1) % scq->length;
    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d)\n", scq->wr_ptr, &((scq->queue)[-(scq->wr_ptr)]), (scq->queue)[-(scq->wr_ptr)].time, (scq->queue)[-(scq->wr_ptr)].truth);
    return R2U2_OK;
  }
  if (((scq->queue)[-((scq->wr_ptr - 1) % scq->length)].truth == res->truth) && \
      ((scq->queue)[-((scq->wr_ptr - 1) % scq->length)].time < res->time)) {
    R2U2_DEBUG_PRINT("\t\tAggregate Write\n");
    // Aggregate write, overwrite to update timestamp
    (scq->queue)[-((scq->wr_ptr - 1) % scq->length)] = *res;
    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d)\n", scq->wr_ptr, &((scq->queue)[-(scq->wr_ptr)]), (scq->queue)[-(scq->wr_ptr)].time, (scq->queue)[-(scq->wr_ptr)].truth);
    return R2U2_OK;
  } else {
    // Standard write
    R2U2_DEBUG_PRINT("\t\tStandard Write\n");
    (scq->queue)[-(scq->wr_ptr)] = *res;
    scq->wr_ptr = (scq->wr_ptr + 1) % scq->length;
    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d)\n", scq->wr_ptr, &((scq->queue)[-(scq->wr_ptr)]), (scq->queue)[-(scq->wr_ptr)].time, (scq->queue)[-(scq->wr_ptr)].truth);
    return R2U2_OK;
  }
  return R2U2_ERR_OTHER;
}

r2u2_verdict r2u2_scq_pop(r2u2_scq_t *scq, r2u2_time *rd_ptr) {
  // TODO(bckempa): This is a misnomer, it's a peek not a pop

  // This is an obvious inlining candidate
  return (scq->queue)[-(*rd_ptr)];
}

// TODO(bckempa): Maybe it makes sense to pair the read pointers and desired times?
//                Need to verify algotihmic implication, though may reduce redundent data
r2u2_bool r2u2_scq_is_empty(r2u2_scq_t *scq, r2u2_time *rd_ptr, r2u2_time *desired_time_stamp) {

  // NOTE: This should be the child SCQ, but the parent's read ptr
  // this ensureds CSE works by allowing many readers

  R2U2_TRACE_PRINT("\t\tSCQ Empty Check\n");

  if ((scq->queue)[-(*rd_ptr)].time >= *desired_time_stamp) {
    // New data availabe
    R2U2_TRACE_PRINT("\t\tNew data found in place t=%d >= %d)\n", (scq->queue)[-(*rd_ptr)].time, *desired_time_stamp);
    return false;
  } else if (*rd_ptr != scq->wr_ptr) {

    // Fast-forword queue
    while ((*rd_ptr != scq->wr_ptr) && ((scq->queue)[-(*rd_ptr)].time < *desired_time_stamp)) {
      R2U2_TRACE_PRINT("\t\tScanning queue t=%d < %d\n", (scq->queue)[-(*rd_ptr)].time, *desired_time_stamp);
      *rd_ptr = (*rd_ptr + 1) % scq->length;
    }

    if ((scq->queue)[-(*rd_ptr)].time < *desired_time_stamp) {
      *rd_ptr = (*rd_ptr - 1) % scq->length;
      R2U2_TRACE_PRINT("\t\tNew data found after scanning t=%d\n", (scq->queue)[-(*rd_ptr)].time);
      return true;
    } else {
      R2U2_TRACE_PRINT("\t\tNo new data found after scanning t=%d\n", (scq->queue)[-(*rd_ptr)].time);
      return false;
    }

  } else { // Empty queue - read == write ptr, current value stale
    R2U2_TRACE_PRINT("\t\tEmpty Queue Rd == Wrt and t=%d < %d\n", (scq->queue)[-(*rd_ptr)].time, *desired_time_stamp);
    return true;
  }

  return R2U2_OK;
}
