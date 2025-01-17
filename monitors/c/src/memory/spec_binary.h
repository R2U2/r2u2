#ifndef R2U2_MEMORY_SPEC_BIN_H
#define R2U2_MEMORY_SPEC_BIN_H

#include "r2u2.h"

// Specification binary format handeling
// The specification binary format requires a "blob" which conatins the raw
// bytes, a instruction table is then built to assist in reading the blob.
// This two pass approach enables variable length commands to be addressed
// in constant time rather than linear time during evalution.
//
// NOTE: However you provide the blob (file read into memory, static array,
//       etc.) it must stay in place after the instruction table is built.

typedef uint8_t r2u2_spec_binary_blob[];

typedef struct {
  // The current binary format only supports the first 256 addressable engine types
  uint8_t engine_tag;
  void*   instruction;
  size_t  instruction_length;
} r2u2_spec_instruction_metadata;

typedef r2u2_spec_instruction_metadata r2u2_spec_instruction_table[];

#endif /* R2U2_MEMORY_SPEC_BIN_H */
