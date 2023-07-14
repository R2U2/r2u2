#ifndef R2U2_ENGINES_H
#define R2U2_ENGINES_H

#include <stdio.h>

#include "internals/errors.h"
#include "internals/types.h"

#include "memory/monitor.h"

typedef enum {
    R2U2_ENG_NA = 0, // Null instruction tag - acts as ENDSEQ
    R2U2_ENG_SY = 1, // System commands - reserved for monitor control
    R2U2_ENG_CG = 2, // Immediate Configuration Directive
    R2U2_ENG_AT = 3, // Original Atomic Checker
    R2U2_ENG_TL = 4, // MLTL Temporal logic engine
    R2U2_ENG_BZ = 5, // Booleanizer
} r2u2_engine_tag_t;
// TODO(bckempa): Setup debug assert s.t. enum must fit
//
// These are int tags by default, which is waaaaay bigger than required
// TODO(bckempa): Limit to one byte (256 engine types?)

r2u2_status_t r2u2_instruction_dispatch(r2u2_monitor_t *monitor);


#endif /* R2U2_ENGINES_H */
