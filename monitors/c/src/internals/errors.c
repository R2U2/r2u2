#include "errors.h"

#if R2U2_DEBUG
#include <assert.h>
#endif

#if R2U2_DEBUG


// static here means only visable within the file
static const char* const R2U2_STATUS_STRINGS[] = {
    "R2U2 OK",
    "R2U2 Unspecificed Error",
};

const char* r2u2_status_string(r2u2_status_t status) {
  assert(status < R2U2_STATUS_COUNT);
  return R2U2_STATUS_STRINGS[status];
}

#endif
