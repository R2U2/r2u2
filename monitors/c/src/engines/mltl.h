#ifndef R2U2_ENGINES_MLTL_H
#define R2U2_ENGINES_MLTL_H

#include "../instructions/mltl.h"
#include "../memory/monitor.h"
#include "../internals/errors.h"

/// @brief      Updates the BZ engine based on current instruction in table
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @return     r2u2_status_t
r2u2_status_t r2u2_mltl_update(r2u2_monitor_t* monitor);

/// @brief      Configures the MLTL engine (prior to execution) based on a r2u2_mltl_instruction_t with a configure flag
/// @param[in]  monitor  Pointer to r2u2_monitor_t
/// @param[in]  instr  Pointer to r2u2_mltl_instruction_t (i.e., configure instruction)
/// @return     r2u2_status_t
r2u2_status_t r2u2_mltl_configure_instruction_dispatch(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t* instr);

#endif /* R2U2_ENGINES_MLTL_H */
