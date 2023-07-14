#ifndef R2U2_ENGINES_BINARY_LOAD_H
#define R2U2_ENGINES_BINARY_LOAD_H

#include "r2u2.h"

// Reads from spec binary, filling out instruction memory and instruction table

// Because instructions aren't read form inst mem sequentially but are directed
// by the inst table instead, we can just place the whole binary into the inst
// mem instead of having a separate, largely identical, blob array

/// @brief      Populate inst table from inst memory, processing monitor cmds
/// @param[in]  monitor  Pointer to monitor loaded with spec binary in inst mem
/// @return     r2u2_status
r2u2_status_t r2u2_process_binary(r2u2_monitor_t *monitor);

#endif /* R2U2_ENGINES_BINARY_LOAD_H */
