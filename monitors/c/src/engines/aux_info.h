#ifndef AUX_INFO_H
#define AUX_INFO_H

#include "memory/monitor.h"
#include "instructions/aux_info.h"

r2u2_status_t r2u2_aux_formula_report(r2u2_monitor_t *, r2u2_mltl_instruction_t, r2u2_verdict);

r2u2_status_t r2u2_aux_contract_report(r2u2_monitor_t *, r2u2_mltl_instruction_t, r2u2_verdict);

#endif