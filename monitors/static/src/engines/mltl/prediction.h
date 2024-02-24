#ifndef R2U2_ENGINES_MLTL_FT_PREDICTION_H
#define R2U2_ENGINES_MLTL_FT_PREDICTION_H

#include "r2u2.h"

#include "mltl.h"
#include "booleanizer.h"
#include "stdlib.h"

typedef struct {
  r2u2_time rd_ptr;
  r2u2_time rd_ptr2;
  r2u2_time desired_time_stamp;
  r2u2_time edge;
  r2u2_time max_out;
  r2u2_verdict previous;
} r2u2_scq_state_t;

r2u2_verdict get_predicted_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n);
r2u2_bool predicted_operand_data_ready(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n);
r2u2_status_t r2u2_mltl_ft_predict(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_verdict* scq_prob_buffer);
r2u2_status_t r2u2_bz_predict(r2u2_monitor_t *monitor, r2u2_bz_instruction_t *instr, r2u2_time k_mode, float prob);
r2u2_status_t find_child_instructions(r2u2_monitor_t *monitor, r2u2_instruction_t *instr, r2u2_mltl_instruction_t** mltl_instructions, size_t *mltl_size, r2u2_bz_instruction_t** bz_instructions, size_t *bz__size, uint8_t difference);
void find_trace_start_index(r2u2_monitor_t *monitor, r2u2_time* trace_start_index, size_t size);
void prep_prediction_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size);
void restore_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size);
void prep_prediction_prob(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_verdict** scq_prob_buffer, size_t size);

#endif /* R2U2_ENGINES_MLTL_FT_PREDICTION_H */
