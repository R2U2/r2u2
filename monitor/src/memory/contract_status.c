#include "r2u2.h"

#include "contract_status.h"

#include "engines/mltl/mltl.h"

r2u2_status_t r2u2_contract_status_load_mapping(r2u2_contract_status_reporter_t *status_reporter, r2u2_monitor_t *monitor) {
  // TODO(bckempa): We need to extract this to a higher level as more members of the aux system return

  char type;
  size_t c_num=0, offset=0, length=0;
  (status_reporter->aux_con_map)[0] = status_reporter->aux_con_arena;
  uint8_t* data = *monitor->instruction_mem;

  // Jump past instuction data to alias segment
  R2U2_DEBUG_PRINT("Aux: Scanning instruction_mem for definitions\n");
  while (data[offset] != 0) { offset += data[offset]; }
  offset += data[offset]; // Once more to start at the first ASCII in the aux

  do {
    // Length encodes size of processed string not including null
    // so we move forwrod by length +1 to jump each string
    // This initial 0 + 1 moves us past the final zero offset of the inst mem
    // if length is zero at the end of a loop, nothing was found so serach ends
    offset += length + 1;
    if (sscanf((char*)&(data[offset]), "%c", &type) == 1) {
      switch(type){
      case 'C': {
        sscanf((char*)&(data[offset]), "%*c %s %zu %zu %zu", (status_reporter->aux_con_map)[c_num], &((status_reporter->aux_con_forms)[3*c_num]), &((status_reporter->aux_con_forms)[3*c_num+1]), &((status_reporter->aux_con_forms)[3*c_num+2]));
        (status_reporter->aux_con_map)[c_num+1] = (status_reporter->aux_con_map)[c_num] + strlen((status_reporter->aux_con_map)[c_num]) + 1; // Leave a Null
        R2U2_DEBUG_PRINT("Mapping contract: %s\n", (status_reporter->aux_con_map)[c_num]);
        c_num++;
        // TODO(bckempa): Get clever with this, use %n from the sscanf to set
        length = strlen((char*)&(data[offset]));
        break;
      }
      case 'F': {
        R2U2_DEBUG_PRINT("Aux: No handler enabled for type %c\n", type);
        length = strlen((char*)&(data[offset]));
        break;
      }
      case 'R': {
        R2U2_DEBUG_PRINT("Aux: No handler enabled for type %c\n", type);
        length = strlen((char*)&(data[offset]));
        break;
      }
      default: {
        R2U2_DEBUG_PRINT("Aux: Invalid type '%c' - end of search\n", type);
        length = 0;
        break;
      }
      }
    } else {
        // Error scanning type char, end search
        R2U2_DEBUG_PRINT("Aux: Cannot read type end of search\n");
        length = 0;
    }
  } while (length != 0);

  status_reporter->aux_con_max = c_num;
  R2U2_DEBUG_PRINT("Loaded %d contracts\n", c_num);

  return R2U2_OK;
}

r2u2_status_t r2u2_contract_status_report(r2u2_contract_status_reporter_t *status_reporter, r2u2_instruction_t *inst, r2u2_verdict *res) {

  // Right now contracts are only supported by the TL engine so we can cast to mltl inst
  // There is a good argument that this belongs in an engine since it needs other engine details
  for (size_t i = 0; i < 3*(status_reporter->aux_con_max); ++i) {
    if (((r2u2_mltl_instruction_t*)(inst->instruction_data))->op2.value == (status_reporter->aux_con_forms)[i]) {
      switch(i%3){
        case 0: {
          if(!(res->truth)){
            fprintf(status_reporter->out_file, "Contract %s inactive at %d\n", (status_reporter->aux_con_map)[i/3], res->time);
          }
          break;
        }
        case 1: {
          if(!(res->truth)){
            fprintf(status_reporter->out_file, "Contract %s invalid at %d\n", (status_reporter->aux_con_map)[i/3], res->time);
          }
          break;
        }
        case 2: {
          if(res->truth){
            fprintf(status_reporter->out_file, "Contract %s verified at %d\n", (status_reporter->aux_con_map)[i/3], res->time);
          }
          break;
        }
      }
      /* We'd like to stop searching after a contract has been found
       * but there could be formula reuse - specifically of assumptions
      */
      // i = 3*aux_con_max;
    }
  }

  return R2U2_OK;
}
