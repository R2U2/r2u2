#ifndef R2U2_ENGINES_MLTL_FT_PREDICTION_H
#define R2U2_ENGINES_MLTL_FT_PREDICTION_H

#include "r2u2.h"

#include "mltl.h"
#include "booleanizer.h"
#include "stdlib.h"

#if R2U2_PRED_PROB

typedef struct {
  r2u2_tnt_t read1;
  r2u2_tnt_t read2;
  r2u2_tnt_t next_time;
  r2u2_tnt_t edge;
  r2u2_tnt_t previous;
} r2u2_scq_state_t;

r2u2_status_t find_child_instructions(r2u2_monitor_t *monitor, r2u2_instruction_t *instr, r2u2_mltl_instruction_t** mltl_instructions, size_t *mltl_size, r2u2_instruction_t** load_instructions, size_t *load_size, uint8_t difference);
void prep_prediction_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_mltl_instruction_t* return_instr, r2u2_scq_state_t* prev_real_state, size_t size);
void restore_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_mltl_instruction_t* return_instr, r2u2_scq_state_t* prev_real_state, size_t size);

#endif /* R2U2_ENGINES_MLTL_FT_PREDICTION_H */
#endif
