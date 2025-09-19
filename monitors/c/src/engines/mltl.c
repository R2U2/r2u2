#include "internals/config.h"
#include "mltl.h"
#if R2U2_AUX_STRING_SPECS
#include "engines/aux_info.h"
#endif
#include "internals/debug.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))
#define sub_min_zero(x,y) (((x)<(y))?(0):((x)-(y)))

/// @brief      Check for and retrieve an instruction operand's next value
/// @param[in]  monitor Pointer to (configured) R2U2 monitor
/// @param[in]  instr Pointer to r2u2_mltl_instruction_t (i.e., the parent node)
/// @param[in]  op_num Indicating left (op_num = 0) or right (op_num = 1) child
/// @param[out] result Verdict-timestamp tuple that was read from SCQ (passed-by-reference)
/// @return     r2u2_bool Indicates if data is ready and `result` is valid
static r2u2_bool check_operand_data(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t* instr, r2u2_bool op_num, r2u2_verdict* result) {
    // Get operand info based on `op_num` which indicates left/first v.s. right/second
    uint8_t op_type = (op_num == 0) ? (instr->op1_type) : (instr->op2_type);
    uint32_t value = (op_num == 0) ? (instr->op1_value) : (instr->op2_value);

    switch (op_type) {
      case R2U2_FT_OP_DIRECT:
        if (instr->opcode == R2U2_MLTL_OP_SINCE || instr->opcode == R2U2_MLTL_OP_TRIGGER){
          r2u2_scq_temporal_block_t* temp = r2u2_scq_temporal_get(monitor->queue_arena, instr->memory_reference);
          if (value) {
            *result = set_verdict_true(monitor->time_stamp + temp->upper_bound);
          } else {
            *result = set_verdict_false(monitor->time_stamp + temp->upper_bound);
          }
        } else {
          if (value) {
            *result = set_verdict_true(monitor->time_stamp);
          } else {
            *result = set_verdict_false(monitor->time_stamp);
          }
        }
        return true;

      case R2U2_FT_OP_ATOMIC:
        // Only load in atomics on first loop of time step
        if (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP){
          if ((monitor->atomic_buffer)[value]) {
            *result = *result = set_verdict_true(monitor->time_stamp);
          } else {
            *result = set_verdict_false(monitor->time_stamp);
          }
          return true;
        } else {
          return false;
        }

      case R2U2_FT_OP_SUBFORMULA:
        // Handled by the shared_connection queue check function, just need the arguments
        return r2u2_scq_read(monitor->queue_arena, instr->memory_reference, value, op_num, result);

      case R2U2_FT_OP_NOT_SET:
        *result = 0;
        return false;

      default:
        R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
        *result = 0;
        return false;
    }
}

/// @brief      Push new result to SCQ
/// @param[in]  monitor Pointer to (configured) R2U2 monitor
/// @param[in]  instr Pointer to r2u2_mltl_instruction_t (i.e., the node being written to)
/// @param[out] result Verdict-timestamp tuple to be written to SCQ
/// @return     r2u2_status_t
static r2u2_status_t push_result(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t* instr, r2u2_verdict result) {
  // Pushes result to queue, sets next_time, and flags progress if needed

  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {
    monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;
  }

  r2u2_scq_write(monitor->queue_arena, instr->memory_reference, result);
  R2U2_DEBUG_PRINT("\t(%d,%s)\n", get_verdict_time(result), (get_verdict_truth(result)) ? "T" : "F" );

  return R2U2_OK;
}

r2u2_status_t r2u2_mltl_update(r2u2_monitor_t* monitor) {

  r2u2_mltl_instruction_t* instr = &(monitor->mltl_instruction_tbl[monitor->mltl_program_count.curr_program_count]);

  r2u2_bool op0_rdy, op1_rdy;
  r2u2_verdict op0, op1, result;
  r2u2_status_t error_cond;

  r2u2_scq_control_block_t* ctrl = &(monitor->queue_arena.control_blocks[instr->memory_reference]);
  r2u2_scq_temporal_block_t* temp; // Only utilized for temporal operators

  switch (instr->opcode) {

    /* Control Commands */
    case R2U2_MLTL_OP_NOP: {
      R2U2_DEBUG_PRINT("\tFT NOP\n");
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_LOAD: {
      R2U2_DEBUG_PRINT("\tFT LOAD\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        push_result(monitor, instr, op0);
        ctrl->next_time = get_verdict_time(op0)+1;
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_RETURN: {
      R2U2_DEBUG_PRINT("\tFT RETURN\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        R2U2_DEBUG_PRINT("\t(%d,%s)\n", get_verdict_time(op0), (get_verdict_truth(op0)) ? "T" : "F");

        //push_result(monitor, instr, op0);
        ctrl->next_time = get_verdict_time(op0)+1;

        if (monitor->out_file != NULL) {
          #if R2U2_AUX_STRING_SPECS
            r2u2_aux_formula_report(monitor, *instr, op0);
            r2u2_aux_contract_report(monitor, *instr, op0);
          #else
            fprintf(monitor->out_file, "%d:%u,%s\n", instr->op2_value, get_verdict_time(op0), (get_verdict_truth(op0)) ? "T" : "F");
          #endif
        }

        if (monitor->out_func != NULL) {
          (monitor->out_func)(*instr, &op0);
        }

        if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {
          monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;
        }
      }

      error_cond = R2U2_OK;
      break;
    }

    /* Future Temporal Observers */
    case R2U2_MLTL_OP_EVENTUALLY: {
      R2U2_DEBUG_PRINT("\tFT EVENTUALLY\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_GLOBALLY: {
      R2U2_DEBUG_PRINT("\tFT GLOBALLY\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_UNTIL: {
      R2U2_DEBUG_PRINT("\tFT UNTIL\n");
      temp = r2u2_scq_temporal_get(monitor->queue_arena, instr->memory_reference);
      if (ctrl->next_time < temp->lower_bound){
        ctrl->next_time = temp->lower_bound;
      }
      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (get_verdict_truth(op1)) {
          R2U2_DEBUG_PRINT("\tRight Op True\n");
          result = set_verdict_true(get_verdict_time(op1) - temp->lower_bound);
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(op1)+1;
          temp->previous = result;
          error_cond = R2U2_OK;
          break;
        }
        if (op0_rdy) {
          r2u2_time tau = min(get_verdict_time(op0), get_verdict_time(op1));
          ctrl->next_time = tau+1;
          if (!(get_verdict_truth(op0))){
            R2U2_DEBUG_PRINT("\tLeft and Right Op False\n");
            result = set_verdict_false(tau - temp->lower_bound);
            push_result(monitor, instr, result);
            ctrl->next_time = tau+1;
            temp->previous = set_verdict_true(result);
            error_cond = R2U2_OK;
            break;
          }
        }
        if (get_verdict_time(op1) >= get_verdict_time(temp->previous) + temp->upper_bound){
          result = set_verdict_false(get_verdict_time(op1) - temp->upper_bound);
          // To handle startup behavior, the truth bit of the previous result
          // storage is used to flag that an ouput has been produced, which can
          // differentiate between a value of 0 for no output vs output produced.
          // Note: Since only the timestamp of the previous result is ever checked,
          // this overloading of the truth bit doesn't cause confict with other logic 
          // and preserves startup behavior.
          if ((get_verdict_time(result) > get_verdict_time(temp->previous)) || \
            ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
            r2u2_time next = max(ctrl->next_time, get_verdict_time(result) + temp->lower_bound + 1);
            R2U2_DEBUG_PRINT("\tRight Op False and Time elapsed\n");
            push_result(monitor, instr, result);
            ctrl->next_time = next;
            temp->previous = set_verdict_true(result);
          }
        }
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_RELEASE: {
      R2U2_DEBUG_PRINT("\tFT RELEASE\n");
      temp = r2u2_scq_temporal_get(monitor->queue_arena, instr->memory_reference);
      if (ctrl->next_time < temp->lower_bound){
        ctrl->next_time = temp->lower_bound;
      }
      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (!(get_verdict_truth(op1))) {
          R2U2_DEBUG_PRINT("\tRight Op False\n");
          result = set_verdict_false(get_verdict_time(op1) - temp->lower_bound);
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(op1)+1;
          temp->previous = set_verdict_true(result);
          error_cond = R2U2_OK;
          break;
        }
        if (op0_rdy) {
          r2u2_time tau = min(get_verdict_time(op0), get_verdict_time(op1));
          ctrl->next_time = tau+1;
          if (get_verdict_truth(op0)){
            R2U2_DEBUG_PRINT("\tLeft and Right Op True\n");
            result = set_verdict_true(tau - temp->lower_bound);
            push_result(monitor, instr, result);
            ctrl->next_time = tau+1;
            temp->previous = result;
            error_cond = R2U2_OK;
            break;
          }
        }
        if (get_verdict_time(op1) >= (get_verdict_time(temp->previous)) + temp->upper_bound){
          result = set_verdict_true(get_verdict_time(op1) - temp->upper_bound);
          // To handle startup behavior, the truth bit of the previous result
          // storage is used to flag that an ouput has been produced, which can
          // differentiate between a value of 0 for no output vs output produced.
          // Note: Since only the timestamp of the previous result is ever checked,
          // this overloading of the truth bit doesn't cause confict with other logic 
          // and preserves startup behavior.
          if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
            ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
            r2u2_time next = max(ctrl->next_time, get_verdict_time(result) + temp->lower_bound + 1);
            R2U2_DEBUG_PRINT("\tRight Op True and Time elapsed\n");
            push_result(monitor, instr, result);
            ctrl->next_time = next;
            temp->previous = result;
          }
        }
      }

      error_cond = R2U2_OK;
      break;
    }
     /* Past Temporal Observers */
    case R2U2_MLTL_OP_ONCE: {
      R2U2_DEBUG_PRINT("\tPT ONCE\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_HISTORICALLY: {
      R2U2_DEBUG_PRINT("\tPT HISTORICALLY\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_SINCE: {
      R2U2_DEBUG_PRINT("\tPT SINCE\n");
      temp = r2u2_scq_temporal_get(monitor->queue_arena, instr->memory_reference);
      if (!(get_verdict_truth(temp->previous)) && (get_verdict_time(temp->previous)) < temp->lower_bound){
        R2U2_DEBUG_PRINT("Not enough data to evaluate at beginning of trace");
        result = set_verdict_false(temp->lower_bound - 1);
        push_result(monitor, instr, result);
        ctrl->next_time = 0;
        temp->previous = set_verdict_true(result);
        error_cond = R2U2_OK;
        break;
      }

      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (get_verdict_truth(op1)) {
          R2U2_DEBUG_PRINT("\tRight Op True\n");
          temp->edge = set_verdict_true(op1);
          ctrl->next_time = get_verdict_time(op1) + 1;
          if (get_verdict_time(op1) >=  sub_min_zero((get_verdict_time(temp->previous)), (temp->lower_bound))){
            result = set_verdict_true(get_verdict_time(op1) + temp->lower_bound);
            // To handle startup behavior, the truth bit of the previous result
            // storage is used to flag that an ouput has been produced, which can
            // differentiate between a value of 0 for no output vs output produced.
            // Note: Since only the timestamp of the previous result is ever checked,
            // this overloading of the truth bit doesn't cause confict with other logic 
            // and preserves startup behavior.
            if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
            ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
              push_result(monitor, instr, result);
              ctrl->next_time = get_verdict_time(op1) + 1;
              temp->previous = result;
              error_cond = R2U2_OK;
              break;
            }
          }
        } else {
          if (!(get_verdict_truth(temp->edge)) || (get_verdict_time(temp->edge)) <= sub_min_zero((get_verdict_time(temp->previous)), temp->upper_bound) && (get_verdict_time(temp->previous)) >= temp->upper_bound){
            ctrl->next_time = get_verdict_time(op1) + 1;
            if (get_verdict_time(op1) >= sub_min_zero((get_verdict_time(temp->previous)), temp->lower_bound)){
              result = set_verdict_false(get_verdict_time(op1) + temp->lower_bound);
              if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
              ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
                R2U2_DEBUG_PRINT("\tRight Op never true from [i-ub,i-lb]\n");
                push_result(monitor, instr, result);
                ctrl->next_time = get_verdict_time(op1) + 1;
                temp->previous = set_verdict_true(result);
                error_cond = R2U2_OK;
                break;
              }
            }
          }
          if (op0_rdy && !(get_verdict_truth(op0))){
            ctrl->next_time = get_verdict_time(op1) + 1;
            if (get_verdict_time(op1) >= sub_min_zero((get_verdict_time(temp->previous)), temp->lower_bound)){
              result = set_verdict_false(get_verdict_time(op1) + temp->lower_bound);
              if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
              ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
                R2U2_DEBUG_PRINT("\tBoth False\n");
                push_result(monitor, instr, result);
                ctrl->next_time = get_verdict_time(op1) + 1;
                temp->previous = set_verdict_true(result);
                error_cond = R2U2_OK;
                break;
              }
            }
          }
        }
      }
      if (op0_rdy && get_verdict_truth(op0) && \
        get_verdict_time(op0) >= sub_min_zero((get_verdict_time(temp->previous)), temp->lower_bound) && get_verdict_truth(temp->edge) && \
        ((get_verdict_time(temp->edge)) > sub_min_zero((get_verdict_time(temp->previous)), temp->upper_bound) || (get_verdict_time(temp->previous)) < temp->upper_bound)) {
        result = set_verdict_true(min(get_verdict_time(op0) + temp->lower_bound, (get_verdict_time(temp->edge)) + temp->upper_bound));
          if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
            ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
              R2U2_DEBUG_PRINT("\tLeft Op True Since Right Op True\n");
              r2u2_time next = max(ctrl->next_time, sub_min_zero(get_verdict_time(result), temp->upper_bound) + 1);
              push_result(monitor, instr, result);
              ctrl->next_time = next;
              temp->previous = result;
              error_cond = R2U2_OK;
              break;
          }
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_TRIGGER: {
      R2U2_DEBUG_PRINT("\tPT TRIGGER\n");
      temp = r2u2_scq_temporal_get(monitor->queue_arena, instr->memory_reference);
      if (!(get_verdict_truth(temp->previous)) && (get_verdict_time(temp->previous)) < temp->lower_bound){
        R2U2_DEBUG_PRINT("Not enough data to evaluate at beginning of trace");
        result = set_verdict_true(temp->lower_bound - 1);
        push_result(monitor, instr, result);
        ctrl->next_time = 0;
        temp->previous = result;
        error_cond = R2U2_OK;
        break;
      }

      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (!(get_verdict_truth(op1))) {
          R2U2_DEBUG_PRINT("\tRight Op False\n");
          temp->edge = set_verdict_true(op1);
          ctrl->next_time = get_verdict_time(op1) + 1;
          if (get_verdict_time(op1) >= sub_min_zero((get_verdict_time(temp->previous)), (temp->lower_bound))){
            result = set_verdict_false(get_verdict_time(op1) + temp->lower_bound);
            // To handle startup behavior, the truth bit of the previous result
            // storage is used to flag that an ouput has been produced, which can
            // differentiate between a value of 0 for no output vs output produced.
            // Note: Since only the timestamp of the previous result is ever checked,
            // this overloading of the truth bit doesn't cause confict with other logic 
            // and preserves startup behavior.
            if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
            ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
              push_result(monitor, instr, result);
              ctrl->next_time = get_verdict_time(op1) + 1;
              temp->previous = set_verdict_true(result);
              error_cond = R2U2_OK;
              break;
            }
          }
        } else {
          if (!(get_verdict_truth(temp->edge)) || (get_verdict_time(temp->edge)) <= sub_min_zero((get_verdict_time(temp->previous)),temp->upper_bound) && (get_verdict_time(temp->previous)) >= temp->upper_bound){
            ctrl->next_time = get_verdict_time(op1) + 1;
            if (get_verdict_time(op1) >= sub_min_zero((get_verdict_time(temp->previous)), temp->lower_bound)){
              result = set_verdict_true(get_verdict_time(op1) + temp->lower_bound);
              if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
              ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
                R2U2_DEBUG_PRINT("\tRight Op true from [i-ub,i-lb]\n");
                push_result(monitor, instr, result);
                ctrl->next_time = get_verdict_time(op1) + 1;
                temp->previous = result;
                error_cond = R2U2_OK;
                break;
              }
            }
          }
          if (op0_rdy && get_verdict_truth(op0)){
            ctrl->next_time = get_verdict_time(op1) + 1;
            if (get_verdict_time(op1) >= sub_min_zero((get_verdict_time(temp->previous)), temp->lower_bound)){
              result = set_verdict_true(get_verdict_time(op1) + temp->lower_bound);
              if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
              ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
                R2U2_DEBUG_PRINT("\tBoth True\n");
                push_result(monitor, instr, result);
                ctrl->next_time = get_verdict_time(op1) + 1;
                temp->previous = result;
                error_cond = R2U2_OK;
                break;
              }
            }
          }
        }
      }
      if (op0_rdy && !(get_verdict_truth(op0)) && \
        get_verdict_time(op0) >= sub_min_zero((get_verdict_time(temp->previous)), temp->lower_bound) && get_verdict_truth(temp->edge) && \
        ((get_verdict_time(temp->edge)) > sub_min_zero((get_verdict_time(temp->previous)), temp->upper_bound) || (get_verdict_time(temp->previous)) < temp->upper_bound)) {
        R2U2_DEBUG_PRINT("We are here!\n");
        result = set_verdict_false(min(get_verdict_time(op0) + temp->lower_bound, (get_verdict_time(temp->edge)) + temp->upper_bound));
        if ((get_verdict_time(result) > (get_verdict_time(temp->previous))) || \
            ((get_verdict_time(result) == 0) && !(get_verdict_truth(temp->previous)))) {
              R2U2_DEBUG_PRINT("\tLeft Op False Since Right Op False\n");
              r2u2_time next = max(ctrl->next_time, sub_min_zero(get_verdict_time(result), temp->upper_bound) + 1);
              push_result(monitor, instr, result);
              ctrl->next_time = next;
              temp->previous = set_verdict_true(result);
              error_cond = R2U2_OK;
              break;
            }
      }

      error_cond = R2U2_OK;
      break;
    }
    /* Boolean Connectives */
    case R2U2_MLTL_OP_NOT: {
      R2U2_DEBUG_PRINT("\tFT NOT\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        if (get_verdict_truth(op0)) {
          push_result(monitor, instr, set_verdict_false(op0));
          ctrl->next_time = get_verdict_time(op0)+1;
        } else {
          push_result(monitor, instr, set_verdict_true(op0));
          ctrl->next_time = get_verdict_time(op0)+1;
        }
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_AND: {
      R2U2_DEBUG_PRINT("\tAND\n");

      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (op0_rdy && op1_rdy) {
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", get_verdict_time(op0), get_verdict_truth(op0), get_verdict_time(op1), get_verdict_truth(op1));
        if (get_verdict_truth(op0) && get_verdict_truth(op1)){
          R2U2_DEBUG_PRINT("\tBoth True\n");
          result = set_verdict_true(min(get_verdict_time(op0), get_verdict_time(op1)));
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(result)+1;
          error_cond = R2U2_OK;
          break;
        } else if (!(get_verdict_truth(op0)) && !(get_verdict_truth(op1))) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          result = set_verdict_false(max(get_verdict_time(op0), get_verdict_time(op1)));
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(result)+1;
          error_cond = R2U2_OK;
          break;
        }
      }
      if (op0_rdy && !(get_verdict_truth(op0))) {
        R2U2_DEBUG_PRINT("\tLeft False\n");
        push_result(monitor, instr, set_verdict_false(op0));
        ctrl->next_time = get_verdict_time(op0)+1;
      } else if (op1_rdy && !(get_verdict_truth(op1))) {
        R2U2_DEBUG_PRINT("\tRight False\n");
        push_result(monitor, instr, set_verdict_false(op1));
        ctrl->next_time = get_verdict_time(op1)+1;
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_OR: {
      R2U2_DEBUG_PRINT("\tOR\n");
      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (op0_rdy && op1_rdy) {
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", get_verdict_time(op0), get_verdict_truth(op0), get_verdict_time(op1), get_verdict_truth(op1));
        if (get_verdict_truth(op0) && get_verdict_truth(op1)){
          R2U2_DEBUG_PRINT("\tBoth True\n");
          result = set_verdict_true(max(get_verdict_time(op0), get_verdict_time(op1)));
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(result)+1;
          error_cond = R2U2_OK;
          break;
        } else if (!(get_verdict_truth(op0)) && !(get_verdict_truth(op1))) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          result = set_verdict_false(min(get_verdict_time(op0), get_verdict_time(op1)));
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(result)+1;
          error_cond = R2U2_OK;
          break;
        } 
      } 
      if (op0_rdy && get_verdict_truth(op0)) {
        R2U2_DEBUG_PRINT("\tLeft True\n");
        push_result(monitor, instr, set_verdict_true(op0));
        ctrl->next_time = get_verdict_time(op0)+1;
      } else if (op1_rdy && get_verdict_truth(op1)) {
        R2U2_DEBUG_PRINT("\tRight True\n");
        push_result(monitor, instr, set_verdict_true(op1));
        ctrl->next_time = get_verdict_time(op1)+1;
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_IMPLIES: {
      R2U2_DEBUG_PRINT("\tIMPLIES\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_XOR: {
      R2U2_DEBUG_PRINT("\tFT XOR\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_EQUIVALENT: {
      R2U2_DEBUG_PRINT("\tFT EQUIVALENT\n");
      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (op0_rdy && op1_rdy) {
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", get_verdict_time(op0), get_verdict_truth(op0), get_verdict_time(op1), get_verdict_truth(op1));
        if ((get_verdict_truth(op0) && get_verdict_truth(op1)) || \
          (!(get_verdict_truth(op0)) && !(get_verdict_truth(op1)))){
          R2U2_DEBUG_PRINT("\tBoth %s\n", (get_verdict_truth(op0)) ? "T" : "F");
          result = set_verdict_true(min(get_verdict_time(op0), get_verdict_time(op1)));
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(result)+1;
        } else {
          R2U2_DEBUG_PRINT("\t%s not equivalent to %s\n", (get_verdict_truth(op0)) ? "T" : "F", (get_verdict_truth(op1)) ? "T" : "F");
          result = set_verdict_false(min(get_verdict_time(op0), get_verdict_time(op1)));
          push_result(monitor, instr, result);
          ctrl->next_time = get_verdict_time(result)+1;
        }
      }

      error_cond = R2U2_OK;
      break;
    }
    /* Error Case */
    default: {
      R2U2_DEBUG_PRINT("Warning: Bad Inst Type\n");
      error_cond = R2U2_INVALID_INST;
      break;
    }
  }

  return error_cond;
}

r2u2_status_t r2u2_mltl_configure_instruction_dispatch(r2u2_monitor_t* monitor, r2u2_mltl_instruction_t* instr){
    R2U2_DEBUG_PRINT("\tFT Configure\n");
    r2u2_scq_control_block_t* ctrl = &(monitor->queue_arena.control_blocks[instr->memory_reference]);

      switch (instr->op1_type) {
        case R2U2_FT_OP_ATOMIC: {
            ctrl->length = instr->op1_value;

            R2U2_DEBUG_PRINT("\t\tCfg SCQ %u: len = %u\n", instr->memory_reference, ctrl->length);

            /* The first queue doesn't have a previous queue to offset from and can use
            * the slot pointed to by the control block queue pointer, so if the queue id
            * is zero, we use a different offset calculation.
            */
            if (r2u2_unlikely(instr->memory_reference == 0)) {
                // First queue starts at beginning of queue_mem
                ctrl->queue = monitor->queue_arena.queue_mem;
            } else {
                // All subsuquent queues count forward from previous queue
                r2u2_scq_control_block_t prev_ctrl = monitor->queue_arena.control_blocks[instr->memory_reference - 1];
                ctrl->queue = prev_ctrl.queue + prev_ctrl.length;
            }

            if(instr->op2_type == R2U2_FT_OP_ATOMIC){ // Indicates that this is a temporal operator
              // Temporally reserve space for the temporal block metadata
              ctrl->length += R2U2_TEMPORAL_METADATA_SIZE;

              R2U2_DEBUG_PRINT("\t\tCfg SCQ %u: Temp Rsvd Temporal Metadata, len = %u\n", instr->memory_reference, ctrl->length);

            }

            ctrl->queue[0] = r2u2_infinity;

            #if R2U2_DEBUG
            r2u2_scq_queue_print(monitor->queue_arena, instr->memory_reference);
            #endif

            return R2U2_OK;
        }
        case R2U2_FT_OP_SUBFORMULA: {
          // Now that the temporal metadata is reserved (from previous SCQ configure size instruction)
          // shortening length of SCQ to the correct length
          ctrl->length -= R2U2_TEMPORAL_METADATA_SIZE;
          R2U2_DEBUG_PRINT("\t\tCfg SCQ %u: Reset SCQ length, len = %u\n", instr->memory_reference, ctrl->length);
          r2u2_scq_temporal_block_t* temp = r2u2_scq_temporal_get(monitor->queue_arena, instr->memory_reference);
          temp->lower_bound = instr->op1_value;
          temp->upper_bound = instr->op2_value;
          break;
        }
        default: {
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          break;
        }
      }

      return R2U2_OK;
}
