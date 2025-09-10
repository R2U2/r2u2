#ifndef R2U2_MEMORY_SCQ_H
#define R2U2_MEMORY_SCQ_H

#include "internals/types.h"
#include "internals/errors.h"

 typedef struct {
  r2u2_tnt_t edge;
  r2u2_tnt_t previous;
  r2u2_time lower_bound;
  r2u2_time upper_bound;
} r2u2_scq_temporal_block_t;

typedef struct {
  r2u2_addr length;
  r2u2_addr write;
  r2u2_addr read1;
  r2u2_addr read2;
  r2u2_time next_time;
  r2u2_scq_temporal_block_t temporal_block;
  r2u2_tnt_t *queue;
} r2u2_scq_control_block_t;

typedef struct {
  r2u2_scq_control_block_t *control_blocks;
  r2u2_tnt_t *queue_mem;
} r2u2_scq_arena_t;

/* SCQ Read and Write */
r2u2_status_t r2u2_scq_write(r2u2_scq_arena_t arena, r2u2_time queue_id, r2u2_tnt_t value);
r2u2_bool r2u2_scq_read(r2u2_scq_arena_t arena, r2u2_time queue_id, r2u2_addr *read, r2u2_addr next_time, r2u2_tnt_t *value);

#endif /* R2U2_MEMORY_SCQ_H */
