#ifndef R2U2_ERRORS_H
#define R2U2_ERRORS_H

#include "internals/config.h"

typedef enum {
  R2U2_OK = 0,
  R2U2_ERR_OTHER,
  R2U2_STATUS_COUNT,
  R2U2_INVALID_INST,
  R2U2_END_OF_TRACE,
  R2U2_BAD_SPEC,
  R2U2_UNIMPL,
} r2u2_status_t;

#if R2U2_DEBUG

/// @brief      Get descriptive string for an r2u2_status_t
/// @param[in]  status  A valid r2u2_status_t enum value
/// @return     A pointer to the C string describing the given status enum,
///             crashes with assert if status is out of range.
const char* r2u2_status_string(r2u2_status_t status);

#endif

#endif /* R2U2_ERRORS_H */
