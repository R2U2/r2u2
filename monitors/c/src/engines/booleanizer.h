#ifndef R2U2_ENGINES_BOOLEANIZER_H
#define R2U2_ENGINES_BOOLEANIZER_H

#include "memory/monitor.h"
#include "instructions/booleanizer.h"

/// @brief      Updates the BZ engine based on current instruction in table
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @return     r2u2_status_t
r2u2_status_t r2u2_bz_update(r2u2_monitor_t* monitor);

#endif /* R2U2_ENGINES_BOOLEANIZER_H */
