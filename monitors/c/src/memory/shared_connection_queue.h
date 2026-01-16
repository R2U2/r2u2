#ifndef R2U2_MEMORY_SCQ_H
#define R2U2_MEMORY_SCQ_H

#include "../internals/config.h"
#include "../internals/debug.h"
#include "../internals/types.h"
#include "../internals/errors.h"
#include <stdio.h>

 typedef struct {
  r2u2_verdict edge;
  r2u2_verdict previous;
  r2u2_time lower_bound;
  r2u2_time upper_bound;
} r2u2_scq_temporal_block_t;

typedef struct {
  r2u2_addr length;
  r2u2_addr write;
  r2u2_addr read1;
  r2u2_addr read2;
  r2u2_time next_time;
  r2u2_verdict* queue; // Pointer to slice in queue_mem
} r2u2_scq_control_block_t;

typedef struct {
  r2u2_scq_control_block_t* control_blocks; // Array of control blocks
  r2u2_verdict* queue_mem; // Array that stores all SCQ slots + Temporal Block metadata
} r2u2_scq_arena_t;

/// @brief      Write SCQ slot
/// @param[in]  arena  R2U2 SCQ arena (since this is a struct to 2 pointers, this is pass-by-reference)
/// @param[in]  queue_id  ID of SCQ to write to
/// @param[in]  value  Verdict-timestamp tuple to be written to SCQ
/// @return     r2u2_status_t
r2u2_status_t r2u2_scq_write(r2u2_scq_arena_t arena, r2u2_time queue_id, r2u2_verdict value);

/// @brief      Read SCQ slot
/// @param[in]  arena  R2U2 SCQ arena (since this is a struct to 2 pointers, this is pass-by-reference)
/// @param[in]  parent_queue_id  ID of parent SCQ that is trying to read from child node
/// @param[in]  child_queue_id  ID of child SCQ that is being read from
/// @param[in]  read_num Indicating left (read_num = 0) or right (read_num = 1) child
/// @param[in]  result  Verdict-timestamp tuple that was read from SCQ (passed-by-reference)
/// @return     r2u2_bool Indicates if data is ready and `result` is valid
r2u2_bool r2u2_scq_read(r2u2_scq_arena_t arena, r2u2_time parent_queue_id, r2u2_time child_queue_id, r2u2_bool read_num, r2u2_verdict* result);

/// @brief      Inline function that returns temporal metadata block (assumes correct configuration)
/// @param[in]  arena  R2U2 SCQ arena (since this is a struct to 2 pointers, this is pass-by-reference)
/// @param[in]  queue_id  ID of SCQ to retrieve temporal metadata for
/// @return     r2u2_scq_temporal_block_t* Pointer to temporal metadata block
static inline ALWAYS_INLINE r2u2_scq_temporal_block_t* r2u2_scq_temporal_get(r2u2_scq_arena_t arena, r2u2_time queue_id) {
  return (r2u2_scq_temporal_block_t*) (&(arena.control_blocks[queue_id].queue[arena.control_blocks[queue_id].length]));
}

#if R2U2_DEBUG
    static void r2u2_scq_arena_print(r2u2_scq_arena_t arena) {
        R2U2_DEBUG_PRINT("\t\t\tShared Connection Queue Arena:\n\t\t\t\tBlocks: <%p>\n\t\t\t\tQueues: <%p>\n\t\t\t\tSize: %ld\n", arena.control_blocks, arena.queue_mem, ((void*)arena.queue_mem) - ((void*)arena.control_blocks));
    }

    static void r2u2_scq_queue_print(r2u2_scq_arena_t arena, r2u2_time queue_id) {
        r2u2_scq_control_block_t* ctrl = &((arena.control_blocks)[queue_id]);

        R2U2_DEBUG_PRINT("\t\t\tID: |");
        for (r2u2_time i = 0; i < ctrl->length; ++i) {
            R2U2_DEBUG_PRINT(" <%p> |", (void*)&((ctrl->queue)[i]));
        }
        R2U2_DEBUG_PRINT("\n\t\t\t%3d |", queue_id);
        for (r2u2_time i = 0; i < ctrl->length; ++i) {
            R2U2_DEBUG_PRINT("  %s:%9d  |", (get_verdict_truth((ctrl->queue)[i])) ? "T" : "F", get_verdict_time((ctrl->queue)[i]));
        }
        R2U2_DEBUG_PRINT("\n");
    }
#endif

#endif /* R2U2_MEMORY_SCQ_H */
