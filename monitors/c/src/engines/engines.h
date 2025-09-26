#ifndef R2U2_ENGINES_H
#define R2U2_ENGINES_H

#include "../internals/errors.h"
#include "../memory/monitor.h"

// static const uint8_t R2U2_ENG_NA = 0; // Null instruction tag - acts as ENDSEQ
// static const uint8_t R2U2_ENG_SY = 1; // System commands - reserved for monitor control
static const uint8_t R2U2_ENG_CG = 2; // Immediate Configuration Directive
// Original Atomic Checker was 3, but has been removed since v4.0
static const uint8_t  R2U2_ENG_TL = 4; // MLTL Temporal logic engine
static const uint8_t R2U2_ENG_BZ = 5; // Booleanizer


/// @brief      Executes the R2U2 engine for a single time step
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @return     r2u2_status_t
r2u2_status_t r2u2_step(r2u2_monitor_t* monitor);

#endif /* R2U2_ENGINES_H */
