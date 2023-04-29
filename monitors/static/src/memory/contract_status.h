#ifndef R2U2_MEMORY_AGC_STATUS_H
#define R2U2_MEMORY_AGC_STATUS_H

#include <stdio.h>
#include <string.h>

#include "internals/errors.h"
#include "memory/monitor.h"
#include "memory/instruction.h"

// TODO(bckempa): Right now this uses fixed constaints set by bounds.h
// move this to be like monitor.h with pointers in the structu and a macro
// constructor to prevent unnecessary memroy reservation

typedef char* aux_con_map_t[R2U2_MAX_INSTRUCTIONS];
typedef char aux_con_arena_t[R2U2_MAX_AUX_STRINGS];
typedef size_t aux_con_forms_t[R2U2_MAX_INSTRUCTIONS];
typedef size_t aux_con_max_t;

// #if R2U2_TL_Contract_Status
typedef struct {
  FILE *out_file;

  aux_con_map_t   aux_con_map;
  aux_con_arena_t aux_con_arena;
  aux_con_forms_t aux_con_forms;
  aux_con_max_t   aux_con_max;

} r2u2_contract_status_reporter_t;

// #if R2U2_TL_Contract_Status
// #endif

r2u2_status_t r2u2_contract_status_load_mapping(r2u2_contract_status_reporter_t *status_reporter, r2u2_monitor_t *monitor);
r2u2_status_t r2u2_contract_status_report(r2u2_contract_status_reporter_t *status_reporter, r2u2_instruction_t *inst, r2u2_verdict *res);
// #endif

#endif /* R2U2_MEMORY_AGC_STATUS_H */
