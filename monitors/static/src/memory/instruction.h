#ifndef R2U2_MEMORY_INST_H
#define R2U2_MEMORY_INST_H

#include "internals/types.h"

// Instruction memory is a large data blob, to avoid parsing the variable
// width sections each time, we can cache a {tag, ptr} program table

typedef struct {
  // To avoid the chicken-and-egg stand-up of the execution engines and inst memory,
  // and to allow plugin compilation of engines, we use an int instead of enum for the engine tag here
  // C99 section 6.7.2.2 §2: "The expression that defines the value of an enumeration constant shall be an integer constant expression that has a value representable as an int."
  int engine_tag;
  void *instruction_data;
  // size_t  instruction_length;
} r2u2_instruction_t;

// typedef struct {
//   r2u2_instruction_t program_table[];
//   char* program_data;
// } r2u2_instruction_mem_t;

// TODO(bckempa): Arrays are not pointers, list caveats
typedef r2u2_instruction_t (r2u2_instruction_table_t)[];
typedef uint8_t (r2u2_instruction_memory_t)[];

#endif /* R2U2_MEMORY_INST_H */
