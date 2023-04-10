#ifndef R2U2_MEMORY_BOXQ_H
#define R2U2_MEMORY_BOXQ_H

#include "internals/types.h"
#include "internals/errors.h"

// Box queues for past time temporal operators
// TODO(bckempa): Right now we giv everyone a full sized queue,
// this is overkill but C2PO needs to assign PT queue before we can pare down

typedef uint8_t (r2u2_box_queue_memory_t)[];

typedef struct {
  r2u2_time start;
  r2u2_time end;
} r2u2_boxq_intvl_t;

typedef struct {
  // TODO(bckempa): Need better types for this
  r2u2_int   head;
  r2u2_int   tail;
  r2u2_int   length;
  r2u2_boxq_intvl_t *queue;
  r2u2_boxq_intvl_t interval;
} r2u2_boxq_t;

r2u2_status_t r2u2_boxq_reset(r2u2_boxq_t *boxq);
r2u2_status_t r2u2_boxq_push(r2u2_boxq_t *boxq, r2u2_boxq_intvl_t interval);
r2u2_boxq_intvl_t   r2u2_boxq_peek(r2u2_boxq_t *boxq);
r2u2_boxq_intvl_t r2u2_boxq_pop_head(r2u2_boxq_t *boxq);
r2u2_boxq_intvl_t r2u2_boxq_pop_tail(r2u2_boxq_t *boxq);
r2u2_bool     r2u2_boxq_is_empty(r2u2_boxq_t *boxq);
r2u2_bool r2u2_boxq_is_full(r2u2_boxq_t *boxq);

#endif /* R2U2_MEMORY_BOXQ_H */
