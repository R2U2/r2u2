#ifndef R2U2_ERRORS_H
#define R2U2_ERRORS_H

#if R2U2_DEBUG
#include <assert.h>
#endif

// TODO(bckempa): Namespace these values: R2U2_STATUS_ or R2U2_ERR_
typedef enum r2u2_status {
  R2U2_OK = 0,
  R2U2_ERR_OTHER,
  R2U2_STATUS_COUNT,
  R2U2_INVALID_INST,
  R2U2_END_OF_TRACE,
  R2U2_BAD_SPEC,
  R2U2_UNIMPL,
} r2u2_status_t;

#if R2U2_DEBUG

// Only exists in debug
const char *r2u2_status_string(r2u2_status_t status);

#endif

#endif /* R2U2_ERRORS_H */
