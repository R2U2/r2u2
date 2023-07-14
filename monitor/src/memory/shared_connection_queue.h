#ifndef R2U2_MEMORY_SCQ_H
#define R2U2_MEMORY_SCQ_H

#include "internals/types.h"
#include "internals/errors.h"

typedef uint8_t (r2u2_scq_queue_memory_t)[];

typedef struct {
  // TODO(bckempa): Need better types for this
  r2u2_verdict *queue;
  r2u2_time length;
  r2u2_time wr_ptr;
  r2u2_time rd_ptr;
  r2u2_time rd_ptr2;
  r2u2_time desired_time_stamp;
  r2u2_time edge;
  r2u2_time max_out;
  r2u2_time interval_start;
  r2u2_time interval_end;
  r2u2_verdict previous;
} r2u2_scq_t;

r2u2_status_t r2u2_scq_push(r2u2_scq_t *scq, r2u2_verdict *res);
r2u2_verdict r2u2_scq_pop(r2u2_scq_t *scq, r2u2_time *rd_ptr);
r2u2_bool r2u2_scq_is_empty(r2u2_scq_t *scq, r2u2_time *rd_ptr, r2u2_time *desired_time_stamp);

#endif /* R2U2_MEMORY_SCQ_H */
