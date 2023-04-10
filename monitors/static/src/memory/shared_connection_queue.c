#include "r2u2.h"

#include "shared_connection_queue.h"

r2u2_status_t r2u2_scq_push(r2u2_scq_t *scq, r2u2_verdict *res) {
  // TODO(bckempa): Verify compiler removes redundant modulo arith, else inline
  if ((scq->queue)[(scq->wr_ptr)].time == r2u2_infinity) {
    // Initialization behavior
    (scq->queue)[(scq->wr_ptr)] = *res;
    scq->wr_ptr = (scq->wr_ptr + 1) % scq->length;
    return R2U2_OK;
  }
  if (((scq->queue)[((scq->wr_ptr - 1) % scq->length)].truth == res->truth) && \
      ((scq->queue)[((scq->wr_ptr - 1) % scq->length)].time < res->time)) {
    // Aggregate write, overwrite to update timestamp
    (scq->queue)[((scq->wr_ptr - 1) % scq->length)] = *res;
    return R2U2_OK;
  } else {
    // Standard write
    (scq->queue)[(scq->wr_ptr)] = *res;
    scq->wr_ptr = (scq->wr_ptr + 1) % scq->length;
    return R2U2_OK;
  }
}

r2u2_verdict r2u2_scq_pop(r2u2_scq_t *scq, r2u2_time *rd_ptr) {

  // This is an obvious inlining candidate
  return (scq->queue)[*rd_ptr];
}

// TODO(bckempa): Maybe it makes sense to pair the read pointers and desired times?
//                Need to verify algotihmic implication, though may reduce redundent data
r2u2_bool r2u2_scq_is_empty(r2u2_scq_t *scq, r2u2_time *rd_ptr, r2u2_time *desired_time_stamp) {

  // NOTE: This should be the child SCQ, but the parent's read ptr
  // this ensureds CSE works by allowing many readers

  if ((scq->queue)[*rd_ptr].time >= *desired_time_stamp) {
    // New data availabe
    return false;
  } else if (*rd_ptr != scq->wr_ptr) {

    // Fast-forword queue
    while ((*rd_ptr != scq->wr_ptr) && ((scq->queue)[*rd_ptr].time < *desired_time_stamp)) {
      *rd_ptr = (*rd_ptr + 1) % scq->length;
    }

    if ((scq->queue)[*rd_ptr].time < *desired_time_stamp) {
      *rd_ptr = (*rd_ptr - 1) % scq->length;
      return true;
    } else {
      return false;
    }

  } else { // Empty queue - read == write ptr, current value stale
    return true;
  }

  return R2U2_OK;
}
