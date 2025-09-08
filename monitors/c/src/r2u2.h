#ifndef R2U2_H
#define R2U2_H

#include "internals/config.h"
#include "internals/errors.h"
#include "internals/debug.h"
#include "internals/types.h"

#include "memory/monitor.h"

// Options for geting a monitor:
//  1. Hardcode one in
//  2. Read in at runtime:
//     a. into freshly allocated heap memory
//     b. into reservered .bbs space

r2u2_status_t r2u2_init(uint8_t* spec, r2u2_monitor_t *monitor);

/// @brief      Take a step with runtime monitor
/// @param[in]  monitor  Pointer to monitor loaded with spec to step
/// @return     r2u2_status
r2u2_status_t r2u2_step(r2u2_monitor_t *monitor);

#endif
