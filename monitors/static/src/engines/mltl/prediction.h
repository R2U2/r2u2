#ifndef R2U2_ENGINES_MLTL_FT_PREDICTION_H
#define R2U2_ENGINES_MLTL_FT_PREDICTION_H

#include "r2u2.h"

#include "mltl.h"
#include "stdlib.h"

typedef struct {
  r2u2_time rd_ptr;
  r2u2_time rd_ptr2;
  r2u2_time desired_time_stamp;
  r2u2_time edge;
  r2u2_time max_out;
  r2u2_verdict previous;
} r2u2_scq_state_t;

r2u2_status_t find_child_instructions(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_mltl_instruction_t** instructions, size_t *size, uint8_t difference);
r2u2_status_t r2u2_mltl_ft_predict(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr);
void prep_prediction_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size);
void restore_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size);
r2u2_verdict get_predicted_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n);
r2u2_bool predicted_operand_data_ready(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n);


#endif /* R2U2_ENGINES_MLTL_FT_PREDICTION_H */
