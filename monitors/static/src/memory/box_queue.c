#include "r2u2.h"

#include "box_queue.h"

r2u2_status_t r2u2_boxq_reset(r2u2_boxq_t *boxq) {
  boxq->head = 0;
  boxq->tail = 0;
  return R2U2_OK;
}

r2u2_status_t r2u2_boxq_push(r2u2_boxq_t *boxq, r2u2_boxq_intvl_t interval) {

  #if R2U2_DEBUG
    if (r2u2_boxq_is_full(boxq)) {
      R2U2_DEBUG_PRINT("\tWARNING: PT Box Queue Overflow\n");
    }
  #endif

  boxq->queue[boxq->head] = interval;

  boxq->head = (boxq->head + 1) % boxq->length;

  return R2U2_OK;
}

r2u2_boxq_intvl_t r2u2_boxq_peek(r2u2_boxq_t *boxq) {
  //
  if (r2u2_boxq_is_empty(boxq)) {
    return (r2u2_boxq_intvl_t){r2u2_infinity, r2u2_infinity};
  } else {
    return boxq->queue[boxq->tail];
  }
}

r2u2_boxq_intvl_t r2u2_boxq_pop_head(r2u2_boxq_t *boxq) {
  //
  if (r2u2_boxq_is_empty(boxq)) {
    #if R2U2_DEBUG
      R2U2_DEBUG_PRINT("\tWARNING: PT Box Queue Underflow\n");
    #endif
    return (r2u2_boxq_intvl_t){r2u2_infinity, r2u2_infinity};
  } else {
    boxq->head = (boxq->head - 1) % boxq->length;
    return boxq->queue[boxq->head];
  }
}

r2u2_boxq_intvl_t r2u2_boxq_pop_tail(r2u2_boxq_t *boxq) {
  //
  r2u2_int res_index;
  if (r2u2_boxq_is_empty(boxq)) {
    #if R2U2_DEBUG
      R2U2_DEBUG_PRINT("\tWARNING: PT Box Queue Underflow\n");
    #endif
    return (r2u2_boxq_intvl_t){r2u2_infinity, r2u2_infinity};
  } else {
    res_index = boxq->tail;
    boxq->tail = (boxq->tail + 1) % boxq->length;
    return boxq->queue[res_index];
  }
}

// TODO(bckempa): Great inlining candidate
r2u2_bool r2u2_boxq_is_empty(r2u2_boxq_t *boxq) {
  return boxq->head == boxq->tail;
}

r2u2_bool r2u2_boxq_is_full(r2u2_boxq_t *boxq) {
  return ((boxq->head + 1) % boxq->length) == boxq->tail;
}
