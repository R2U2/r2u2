#include "r2u2.h"

#include "register.h"

extern inline void r2u2_atomic_vector_flip(r2u2_atomic_buffer_t buf) {
  // Swap the pointers in the buffer to "move" current values to previous
  r2u2_atomic_vector_t *tmp = buf[1];
  buf[1] = buf[0];
  buf[0] = tmp;

  // TODO(bckempa): Shouldn't need to zero this out, but double check
  // If needed this would have to be done by the caller since we don't know
  // the size here anyway.
}
