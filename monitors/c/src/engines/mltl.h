#ifndef R2U2_ENGINES_MLTL_H
#define R2U2_ENGINES_MLTL_H

#include "r2u2.h"
#include "instructions/mltl.h"

r2u2_status_t r2u2_mltl_instruction_dispatch(r2u2_monitor_t *, r2u2_mltl_instruction_t *);

r2u2_status_t r2u2_mltl_configure_instruction_dispatch(r2u2_monitor_t *, r2u2_mltl_instruction_t *);

#endif /* R2U2_ENGINES_MLTL_H */
