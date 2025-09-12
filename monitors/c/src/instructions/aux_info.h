#ifndef AUX_INFO_INSTRUCTIONS_H
#define AUX_INFO_INSTRUCTIONS_H

#include "internals/errors.h"
#include "internals/types.h"
#include "instructions/mltl.h"
#include "memory/monitor.h"

typedef struct {
    char* spec_str;
    r2u2_addr spec;
} r2u2_formula_aux_info_t;

typedef struct {
    char* spec_str;
    r2u2_addr spec_0;
    r2u2_addr spec_1;
    r2u2_addr spec_2;
} r2u2_contract_aux_info_t;

typedef struct {
  r2u2_formula_aux_info_t *formula_control_blocks;
  r2u2_contract_aux_info_t *contract_control_blocks;
  char *aux_mem;
  size_t max_aux_formula;
  size_t max_aux_contract;
} r2u2_aux_info_arena_t;

#endif