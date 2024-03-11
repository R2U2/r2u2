#ifndef R2U2_MEMORY_SCQ_H
#define R2U2_MEMORY_SCQ_H

#include "internals/types.h"
#include "internals/errors.h"

typedef uint8_t (r2u2_scq_queue_memory_t)[];
typedef uint32_t scq_id_t;

typedef struct {
  // TODO(bckempa): Need better types for this
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
  r2u2_verdict *queue;
} r2u2_scq_t;

/// @brief      Set cir
/// @param[in]  scq  A valid r2u2_status_t enum value
/// @return     A pointer to the C string describing the given status enum,
///             crashes with assert if status is out of range.
// r2u2_status_t r2u2_scq_config_length(r2u2_scq_t *scq, ____ offset, ____ length);

/// @brief      Get descptive string for an r2u2_status
/// @param[in]  status  A valid r2u2_status_t enum value
/// @return     A pointer to the C string describing the given status enum,
///             crashes with assert if status is out of range.
// r2u2_status_t r2u2_scq_config_interval(r2u2_scq_t *scq, ___ lower, ___ upper);

// r2u2_status_t r2u2_scq_reset(r2u2_scq_t *scq);
// r2u2_status_t r2u2_scq_clear(r2u2_scq_t *scq);
// r2u2_status_t r2u2_scq_reset(r2u2_scq_t *scq);

/// @brief      ?
/// @param[in]  foo  ?
/// @param[in]  bar  ?
/// @return     ?
r2u2_status_t r2u2_scq_push(r2u2_scq_t *scq, r2u2_verdict *res);

/// @brief      ?
/// @param[in]  foo  ?
/// @param[in]  bar  ?
/// @return     ?.
r2u2_verdict r2u2_scq_pop(r2u2_scq_t *scq, r2u2_time *rd_ptr);

/// @brief      ?
/// @param[in]  foo  ?
/// @param[in]  bar  ?
/// @return     ?.
r2u2_bool r2u2_scq_is_empty(r2u2_scq_t *scq, r2u2_time *rd_ptr, r2u2_time *desired_time_stamp);

#endif /* R2U2_MEMORY_SCQ_H */
