#ifndef R2U2_ENGINES_PROCESS_BINARY_H
#define R2U2_ENGINES_PROCESS_BINARY_H

#include "internals/errors.h"
#include "memory/monitor.h"

// Reads from spec binary, filling out instruction memory and instruction table

/// @brief      Populate instruction tables from spec
/// @param      spec Pointer to a vector or array of uintt_8 from the specification compiled by C2PO
/// @param[in]  monitor  Pointer to R2U2 monitor
/// @return     r2u2_status
r2u2_status_t r2u2_process_binary(uint8_t* spec, r2u2_monitor_t *monitor);

#endif /* R2U2_ENGINES_PROCESS_BINARY_H */
