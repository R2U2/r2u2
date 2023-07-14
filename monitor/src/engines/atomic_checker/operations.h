#ifndef R2U2_ENGINES_OPERATIONS_H
#define R2U2_ENGINES_OPERATIONS_H

#include "r2u2.h"

#include "atomic_checker.h"
#include "internals/errors.h"

#if R2U2_AT_EXTRA_FILTERS
r2u2_status_t op_abs_diff_angle(r2u2_monitor_t *, r2u2_at_instruction_t *);
r2u2_status_t op_movavg(r2u2_monitor_t *, r2u2_at_instruction_t *);
r2u2_status_t op_rate(r2u2_monitor_t *, r2u2_at_instruction_t *);
#endif

#if R2U2_AT_Signal_Sets
r2u2_status_t op_exactly_one_of(r2u2_monitor_t *, r2u2_at_instruction_t *);
r2u2_status_t op_none_of(r2u2_monitor_t *, r2u2_at_instruction_t *);
r2u2_status_t op_all_of(r2u2_monitor_t *, r2u2_at_instruction_t *);
#endif

r2u2_status_t op_bool(r2u2_monitor_t *, r2u2_at_instruction_t *);
r2u2_status_t op_int(r2u2_monitor_t *, r2u2_at_instruction_t *);
r2u2_status_t op_float(r2u2_monitor_t *, r2u2_at_instruction_t *);

r2u2_status_t op_error(r2u2_monitor_t *, r2u2_at_instruction_t *);

#endif /* R2U2_ENGINES_AT_OPERATIONS_H */
