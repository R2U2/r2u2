#ifndef R2U2_ENGINES_AUX_INFO_H
#define R2U2_ENGINES_AUX_INFO_H

#include "../memory/monitor.h"
#include "../instructions/aux_info.h"

/// @brief      Print the formula status to the monitor.out_file pointer (if possible)
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @param[in]  instr  r2u2_mltl_instruction_t (assumes RETURN instruction) that corresponds gives the result
/// @param[in]  result  Verdict-timestamp tuple result
/// @return     r2u2_status_t
r2u2_status_t r2u2_aux_formula_report(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t instr, r2u2_verdict result);

/// @brief      Print the Assume-Guarantee Contract status to the monitor.out_file pointer (if possible)
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @param[in]  instr  r2u2_mltl_instruction_t (assumes RETURN instruction) that corresponds gives the result
/// @param[in]  result  Verdict-timestamp tuple result
/// @return     r2u2_status_t
r2u2_status_t r2u2_aux_contract_report(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t instr, r2u2_verdict result);

#endif /* R2U2_ENGINES_AUX_INFO_H */