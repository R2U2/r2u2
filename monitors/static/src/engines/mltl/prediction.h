#ifndef R2U2_ENGINES_MLTL_FT_PREDICTION_H
#define R2U2_ENGINES_MLTL_FT_PREDICTION_H

#include "r2u2.h"

#include "mltl.h"
#include "stdlib.h"

r2u2_status_t find_child_instructions(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_mltl_instruction_t** instructions, size_t *size, uint8_t difference);
r2u2_status_t r2u2_mltl_ft_predict(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr);
void prep_prediction_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, size_t size);
void restore_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, size_t size);
r2u2_verdict get_predicted_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n);
r2u2_bool predicted_operand_data_ready(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n);


#endif /* R2U2_ENGINES_MLTL_FT_PREDICTION_H */
