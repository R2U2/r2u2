#ifndef R2U2_H
#define R2U2_H

#include "internals/config.h"
#include "internals/errors.h"
#include "internals/debug.h"
#include "internals/types.h"

#include "memory/monitor.h"

#include "engines/engines.h"

r2u2_status_t r2u2_init(r2u2_monitor_t *monitor);

// Options for geting a monitor:
//  1. Hardcode one in
//  2. Read in at runtime:
//     a. into freshly allocated heap memory
//     b. into reservered .bbs space


/// @brief      Get descptive string for an r2u2_status
/// @param[in]  status  A valid r2u2_status_t enum value
/// @return     A pointer to the C string describing the given status enum,
///             crashes with assert if status is out of range.
r2u2_status_t r2u2_run(r2u2_monitor_t *monitor);

/// @brief      Execute instructions until t_now increments
/// @param[in]  monitor  Pointer to monitor loaded with spec to step
/// @return     r2u2_status
r2u2_status_t r2u2_tic(r2u2_monitor_t *monitor);

/// @brief      Execute all instructions once, might increment t_now
/// @param[in]  monitor  Pointer to monitor loaded with spec to step
/// @return     r2u2_status
r2u2_status_t r2u2_spin(r2u2_monitor_t *monitor);

/// @brief      Execute next instruction
/// @param[in]  monitor  Pointer to monitor loaded with spec to step
/// @return     r2u2_status
r2u2_status_t r2u2_step(r2u2_monitor_t *monitor);

// TODO(bckempa): Macro this - must be done at compile time for .bbs placement
r2u2_status_t r2u2_create_monitor(void);

#endif
