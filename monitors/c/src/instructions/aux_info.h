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
  r2u2_formula_aux_info_t *formula_control_blocks; // Array of formula control blocks
  r2u2_contract_aux_info_t *contract_control_blocks; // Array of contract control blocks
  char *aux_mem; // Array that stores all string data for formulas and contracts
  size_t max_aux_formula; // Number of formulas
  size_t max_aux_contract; // Number of contracts
} r2u2_aux_info_arena_t;

#endif