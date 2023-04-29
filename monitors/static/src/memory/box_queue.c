#include "r2u2.h"

#include "box_queue.h"

// Nominally a First-In, First-Out (FIFO) queue with double-ended pop
// Note the head always points at the next open slot, i.e. not valid data


#if R2U2_DEBUG
static void r2u2_boxq_print(r2u2_boxq_t *boxq) {

  R2U2_DEBUG_PRINT("\t\t\t%*cH\n", (((6 * (ptrdiff_t)boxq->length)-3)-(6 * (boxq->head))), ' ');

  R2U2_DEBUG_PRINT("\t\t\t|");
  for (unsigned int i = 0; i < boxq->length; ++i) {
    if (boxq->queue[(1 - (ptrdiff_t)boxq->length) + i].start == r2u2_infinity) {
      R2U2_DEBUG_PRINT(" INF |");
    } else {
      R2U2_DEBUG_PRINT(" %03d |", boxq->queue[(1 - (ptrdiff_t)boxq->length) + i].start);
    }
  }
  R2U2_DEBUG_PRINT("\n\t\t\t|");
  for (unsigned int i = 0; i < boxq->length; ++i) {
    if (boxq->queue[(1 - (ptrdiff_t)boxq->length) + i].end == r2u2_infinity) {
      R2U2_DEBUG_PRINT(" INF |");
    } else {
      R2U2_DEBUG_PRINT(" %03d |", boxq->queue[(1 - (ptrdiff_t)boxq->length) + i].end);
    }
  }
  R2U2_DEBUG_PRINT(" <%p>\n", boxq->queue);
  R2U2_DEBUG_PRINT("\t\t\t%*cT\n", (((6 * (ptrdiff_t)boxq->length)-3)-(6 * (boxq->tail))), ' ');
}
#endif

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

  boxq->queue[-(ptrdiff_t)boxq->head] = interval;

  boxq->head = (boxq->head == boxq->length-1) ? 0 : boxq->head + 1;

  return R2U2_OK;
}

r2u2_boxq_intvl_t r2u2_boxq_peek(r2u2_boxq_t *boxq) {
  //
  #if R2U2_DEBUG
  r2u2_boxq_print(boxq);
  #endif

  if (r2u2_boxq_is_empty(boxq)) {
    R2U2_DEBUG_PRINT("\t\tEmpty queue, returning (inf, inf)\n");
    return (r2u2_boxq_intvl_t){r2u2_infinity, r2u2_infinity};
  } else {
    return boxq->queue[-(ptrdiff_t)boxq->tail];
  }
}

r2u2_boxq_intvl_t r2u2_boxq_pop_head(r2u2_boxq_t *boxq) {
  //
  if (r2u2_boxq_is_empty(boxq)) {
    #if R2U2_DEBUG
      R2U2_DEBUG_PRINT("\tWARNING: PT Box Queue Head Underflow\n");
    #endif
    R2U2_DEBUG_PRINT("\t\tEmpty queue, returning (inf, inf)\n");
    return (r2u2_boxq_intvl_t){r2u2_infinity, r2u2_infinity};
  } else {
    boxq->head = (boxq->head == 0) ? boxq->length-1 : boxq->head-1;
    return boxq->queue[-(ptrdiff_t)boxq->head];
  }
}

r2u2_boxq_intvl_t r2u2_boxq_pop_tail(r2u2_boxq_t *boxq) {
  //
  r2u2_int res_index;
  if (r2u2_boxq_is_empty(boxq)) {
    #if R2U2_DEBUG
      R2U2_DEBUG_PRINT("\tWARNING: PT Box Queue Tail Underflow\n");
    #endif
    R2U2_DEBUG_PRINT("\t\tEmpty queue, returning (inf, inf)\n");
    return (r2u2_boxq_intvl_t){r2u2_infinity, r2u2_infinity};
  } else {
    res_index = boxq->tail;
    boxq->tail = (boxq->tail == boxq->length-1) ? 0 : boxq->tail + 1;
    return boxq->queue[-(ptrdiff_t)res_index];
  }
}

// TODO(bckempa): Great inlining candidate
r2u2_bool r2u2_boxq_is_empty(r2u2_boxq_t *boxq) {
  return boxq->head == boxq->tail;
}

r2u2_bool r2u2_boxq_is_full(r2u2_boxq_t *boxq) {
  return ((boxq->head + 1) % boxq->length) == boxq->tail;
}
