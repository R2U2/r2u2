#ifndef BZ_BOOLEANIZER_H
#define BZ_BOOLEANIZER_H

#include "memory/monitor.h"
#include "instructions/booleanizer.h"

/// @brief      Updates the BZ engine based on current instruction in table
/// @param[in]  monitor  Pointer to r2u2_monitor_t
/// @return     r2u2_status_t
r2u2_status_t r2u2_bz_update(r2u2_monitor_t* monitor);

#endif
