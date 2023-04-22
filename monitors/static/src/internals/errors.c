#include "errors.h"

#if R2U2_DEBUG


// static here means only visable within the file
static const char* const R2U2_STATUS_STRINGS[] = {
    "R2U2 OK",
    "R2U2 Unspecificed Error",
};

/// @brief      Get descptive string for an r2u2_status
/// @param[in]  status  A valid r2u2_status_t enum value
/// @return     A pointer to the C string describing the given status enum,
///             crashes with assert if status is out of range.
const char* r2u2_status_string(r2u2_status_t status) {
  assert(status < R2U2_STATUS_COUNT);
  return R2U2_STATUS_STRINGS[status];
}

#endif
