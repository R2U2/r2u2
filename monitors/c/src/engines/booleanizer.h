#ifndef BZ_BOOLEANIZER_H
#define BZ_BOOLEANIZER_H

#include <stdint.h>
#include <stdbool.h>

#include "r2u2.h"
#include "internals/types.h"
#include "instructions/booleanizer.h"


r2u2_status_t r2u2_bz_instruction_dispatch(r2u2_monitor_t *, r2u2_bz_instruction_t *);

#endif
