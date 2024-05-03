#ifndef R2U2_MEMORY_REG_H
#define R2U2_MEMORY_REG_H

#include "internals/types.h"

// Includes vectors, buffers, and register files

// typedef struct {
//   // To avoid the chicken-and-egg stand-up of the execution engines and inst memrory,
//   // and to allow plugin compilation of engines, we use an int instead of enum for the engein tag here
//   // C99 section 6.7.2.2 §2: "The expression that defines the value of an enumeration constant shall be an integer constant expression that has a value representable as an int."
//   int engine_tag;
//   int instruction_data;
// } r2u2_instruction_t;

// Register file[n] == Ptr to result of insturction n
// Size == pointer type * num instructions

// TODO(bckempa): Arrays are not pointers, list caveats
// typedef r2u2_register_t (r2u2_register_vector_t)[1]
// typedef r2u2_register_t (r2u2_register_buffer_t)[2]

typedef void* (r2u2_signal_vector_t)[];

typedef r2u2_value_t (r2u2_value_buffer_t)[];

// An atomic vector is an array of booleans representing atomic props,
// the atomic buffer contains the pointers to two atomic vectors with the
// current and previous vector value.
typedef r2u2_bool (r2u2_atomic_vector_t)[];
typedef r2u2_atomic_vector_t *(r2u2_atomic_buffer_t)[2];

typedef r2u2_float (r2u2_atomic_prob_buffer_t)[];

// A k offset vector is an array of indices representing where the next
// mode starts in the trace buffers, the k_offset buffer contains the 
// pointers to two k offset vectors with the signal and atomic buffer 
// k offsets respectively.
typedef r2u2_time (r2u2_k_offset_vector_t)[];
typedef r2u2_k_offset_vector_t *(r2u2_k_offset_buffer_t)[2];

static inline void r2u2_atomic_vector_flip(r2u2_atomic_buffer_t buf) {
  // Swap the pointers in the buffer to "move" current values to previous
  r2u2_atomic_vector_t *tmp = buf[1];
  buf[1] = buf[0];
  buf[0] = tmp;

  // TODO(bckempa): Shouldn't need to zero this out, but double check
  // If needed this would have to be done by the caller since we don't know
  // the size here anyway.
}


#endif /* R2U2_MEMORY_REG_H */
