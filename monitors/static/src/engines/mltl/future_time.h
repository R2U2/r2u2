#ifndef R2U2_ENGINES_MLTL_FT_H
#define R2U2_ENGINES_MLTL_FT_H

#include "r2u2.h"

#include "mltl.h"

r2u2_status_t r2u2_mltl_ft_update(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr);

/// @brief      Get pointer
/// @param[in]  monitor  A valid r2u2_status_t enum value
/// @param[in]  scq  A valid r2u2_status_t enum value
/// @return     A pointer to the r2u2_scq_t struct ...
///             returns NULL if ...
static inline r2u2_scq_t* r2u2_scq_ptr_from_id(r2u2_monitor_t *monitor, scq_id_t id) {

  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[id]);

  #if R2U2_DEBUG
  if (id >= (R2U2_MAX_SCQ_BYTES / sizeof(r2u2_scq_t))) {
    R2U2_DEBUG_PRINT("Warning, SCQ ID out-of-bounds\n");
    scq = NULL;
  }
  #endif

  return scq;
}

#endif /* R2U2_ENGINES_MLTL_FT_H */
