#include "internals/config.h"
#include "mltl.h"
#include "engines/aux_info.h"
#include "internals/debug.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))
#define sub_min_zero(x,y) (((x)<(y))?(0):((x)-(y)))

/// @brief      Check for and retrieve an instruction operand's next value
/// @param[in]  monitor A pointer to the R2U2 monitor
/// @param[in]  instr A pointer to the instruction
/// @param[in]  n Operand to check, 0 for left/first, anything else for right
/// @param[out] result The operand TnT - only vaid if return value is true
/// @return     Boolean indicating if data is ready and `result` is valid
static r2u2_bool check_operand_data(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_bool op_num, r2u2_tnt_t *result) {
    r2u2_scq_arena_t arena = monitor->queue_arena;
    r2u2_scq_control_block_t *ctrl = &(arena.control_blocks[instr->memory_reference]);
    r2u2_addr *rd_ptr; // Hold off on this in case it doesn't exist...

    // Get operand info based on `n` which indicates left/first v.s. right/second
    uint8_t op_type = (op_num == 0) ? (instr->op1_type) : (instr->op2_type);
    uint32_t value = (op_num == 0) ? (instr->op1_value) : (instr->op2_value);

    switch (op_type) {

      case R2U2_FT_OP_DIRECT:
        if (instr->opcode == R2U2_MLTL_OP_SINCE || instr->opcode == R2U2_MLTL_OP_TRIGGER){
          r2u2_scq_temporal_block_t *temp = &(ctrl->temporal_block);
          *result = (monitor->time_stamp + temp->upper_bound) | ((value) ? R2U2_TNT_TRUE : R2U2_TNT_FALSE);
        } else {
          *result = monitor->time_stamp | ((value) ? R2U2_TNT_TRUE : R2U2_TNT_FALSE);
        }
        return true;

      case R2U2_FT_OP_ATOMIC:
        // Only load in atomics on first loop of time step
        // Assuming the cost of the bitops is cheaper than an if branch
        *result = monitor->time_stamp | (((monitor->atomic_buffer)[value]) ? R2U2_TNT_TRUE : R2U2_TNT_FALSE);
        return (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP);

      case R2U2_FT_OP_SUBFORMULA:
        // Handled by the shared_connection queue check function, just need the arguments
        rd_ptr = (op_num == 0) ? &(ctrl->read1) : &(ctrl->read2);

        return r2u2_scq_read(arena, value, rd_ptr, ctrl->next_time, result);

      case R2U2_FT_OP_NOT_SET:
        *result = 0;
        return false;

      default:
        R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
        *result = 0;
        return false;
    }
}

static r2u2_status_t push_result(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_tnt_t result) {
  // Pushes result to queue, sets tau, and flags progress if nedded
  r2u2_scq_arena_t arena = monitor->queue_arena;
  r2u2_scq_control_block_t *ctrl = &(arena.control_blocks[instr->memory_reference]);

  r2u2_scq_write(arena, instr->memory_reference, result);
  R2U2_DEBUG_PRINT("\t(%d,%s)\n", result & R2U2_TNT_TIME, (result & R2U2_TNT_TRUE) ? "T" : "F" );

  ctrl->next_time = (result & R2U2_TNT_TIME)+1;

  // TODO(bckempa): Inline or macro this
  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

  return R2U2_OK;
}

r2u2_status_t r2u2_mltl_instruction_dispatch(r2u2_monitor_t *monitor) {

  r2u2_mltl_instruction_t *instr = &(monitor->mltl_instruction_tbl)[monitor->mltl_program_count.curr_program_count];

  r2u2_bool op0_rdy, op1_rdy;
  r2u2_tnt_t op0, op1, result;
  r2u2_status_t error_cond;

  r2u2_scq_control_block_t *ctrl = &(monitor->queue_arena.control_blocks[instr->memory_reference]);
  r2u2_scq_temporal_block_t *temp; // Only set this if using a temporal op

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
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_RETURN: {
      R2U2_DEBUG_PRINT("\tFT RETURN\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        R2U2_DEBUG_PRINT("\t(%d,%s)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE) ? "T" : "F");

        push_result(monitor, instr, op0);

        if (monitor->out_file != NULL) {
          #if R2U2_AUX_STRING_SPECS
            r2u2_aux_formula_report(monitor, *instr, op0);
            r2u2_aux_contract_report(monitor, *instr, op0);
          #else
            fprintf(monitor->out_file, "%d:%u,%s\n", instr->op2_value, (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE) ? "T" : "F");
          #endif
        }

        if (monitor->out_func != NULL) {
          // TODO(bckempa): Migrate external function pointer interface to use r2u2_tnt_t
          (monitor->out_func)(*instr, &((r2u2_verdict){op0 & R2U2_TNT_TIME, (op0 & R2U2_TNT_TRUE) ? true : false}));
        }

        if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

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
      temp = &(ctrl->temporal_block);
      if (ctrl->next_time < temp->lower_bound){
        ctrl->next_time = temp->lower_bound;
      }
      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (op1 & R2U2_TNT_TRUE) {
          R2U2_DEBUG_PRINT("\tRight Op True\n");
          result = ((op1 & R2U2_TNT_TIME) - temp->lower_bound) | R2U2_TNT_TRUE;
          push_result(monitor, instr, result);
          ctrl->next_time = (op1 & R2U2_TNT_TIME)+1;
          temp->previous = R2U2_TNT_TRUE | result;
          error_cond = R2U2_OK;
          break;
        }
        if (op0_rdy) {
          r2u2_time tau = min(op0 & R2U2_TNT_TIME, op1 & R2U2_TNT_TIME);
          ctrl->next_time = tau+1;
          if (!(op0 & R2U2_TNT_TRUE)){
            R2U2_DEBUG_PRINT("\tLeft and Right Op False\n");
            result = (tau - temp->lower_bound) | R2U2_TNT_FALSE;
            push_result(monitor, instr, result);
            ctrl->next_time = tau+1;
            temp->previous = R2U2_TNT_TRUE | result;
            error_cond = R2U2_OK;
            break;
          }
        }
        if ((op1 & R2U2_TNT_TIME) >= (temp->previous & R2U2_TNT_TIME) + temp->upper_bound){
          result = ((op1 & R2U2_TNT_TIME) - temp->upper_bound) | R2U2_TNT_FALSE;
          // To handle startup behavior, the truth bit of the previous result
          // storage is used to flag that an ouput has been produced, which can
          // differentiate between a value of 0 for no output vs output produced.
          // Note: Since only the timestamp of the previous result is ever checked,
          // this overloading of the truth bit doesn't cause confict with other logic 
          // and preserves startup behavior.
          if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
            (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
            r2u2_time next = max(ctrl->next_time, (result & R2U2_TNT_TIME) + temp->lower_bound + 1);
            R2U2_DEBUG_PRINT("\tRight Op False and Time elapsed\n");
            push_result(monitor, instr, result);
            ctrl->next_time = next;
            temp->previous = R2U2_TNT_TRUE | result;
          }
        }
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_RELEASE: {
      R2U2_DEBUG_PRINT("\tFT RELEASE\n");
      temp = &(ctrl->temporal_block);
      if (ctrl->next_time < temp->lower_bound){
        ctrl->next_time = temp->lower_bound;
      }
      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (!(op1 & R2U2_TNT_TRUE)) {
          R2U2_DEBUG_PRINT("\tRight Op False\n");
          result = ((op1 & R2U2_TNT_TIME) - temp->lower_bound) | R2U2_TNT_FALSE;
          push_result(monitor, instr, result);
          ctrl->next_time = (op1 & R2U2_TNT_TIME)+1;
          temp->previous = R2U2_TNT_TRUE | result;
          error_cond = R2U2_OK;
          break;
        }
        if (op0_rdy) {
          r2u2_time tau = min(op0 & R2U2_TNT_TIME, op1 & R2U2_TNT_TIME);
          ctrl->next_time = tau+1;
          if (op0 & R2U2_TNT_TRUE){
            R2U2_DEBUG_PRINT("\tLeft and Right Op True\n");
            result = (tau - temp->lower_bound) | R2U2_TNT_TRUE;
            push_result(monitor, instr, result);
            ctrl->next_time = tau+1;
            temp->previous = R2U2_TNT_TRUE | result;
            error_cond = R2U2_OK;
            break;
          }
        }
        if ((op1 & R2U2_TNT_TIME) >= (temp->previous & R2U2_TNT_TIME) + temp->upper_bound){
          result = ((op1 & R2U2_TNT_TIME) - temp->upper_bound) | R2U2_TNT_TRUE;
          // To handle startup behavior, the truth bit of the previous result
          // storage is used to flag that an ouput has been produced, which can
          // differentiate between a value of 0 for no output vs output produced.
          // Note: Since only the timestamp of the previous result is ever checked,
          // this overloading of the truth bit doesn't cause confict with other logic 
          // and preserves startup behavior.
          if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
            (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
            r2u2_time next = max(ctrl->next_time, (result & R2U2_TNT_TIME) + temp->lower_bound + 1);
            R2U2_DEBUG_PRINT("\tRight Op True and Time elapsed\n");
            push_result(monitor, instr, result);
            ctrl->next_time = next;
            temp->previous = R2U2_TNT_TRUE | result;
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
      temp = &(ctrl->temporal_block);
      if (!(temp->previous & R2U2_TNT_TRUE) && (temp->previous & R2U2_TNT_TIME) < temp->lower_bound){
        R2U2_DEBUG_PRINT("Not enough data to evaluate at beginning of trace");
        result = (temp->lower_bound - 1) | R2U2_TNT_FALSE;
        push_result(monitor, instr, result);
        ctrl->next_time = 0;
        temp->previous = R2U2_TNT_TRUE | result;
        error_cond = R2U2_OK;
        break;
      }

      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (op1 & R2U2_TNT_TRUE) {
          R2U2_DEBUG_PRINT("\tRight Op True\n");
          temp->edge = (op1 & R2U2_TNT_TIME) | R2U2_TNT_TRUE;
          ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
          if ((op1 & R2U2_TNT_TIME) >=  sub_min_zero((temp->previous & R2U2_TNT_TIME), (temp->lower_bound))){
            result = ((op1 & R2U2_TNT_TIME) + temp->lower_bound) | R2U2_TNT_TRUE;
            // To handle startup behavior, the truth bit of the previous result
            // storage is used to flag that an ouput has been produced, which can
            // differentiate between a value of 0 for no output vs output produced.
            // Note: Since only the timestamp of the previous result is ever checked,
            // this overloading of the truth bit doesn't cause confict with other logic 
            // and preserves startup behavior.
            if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
            (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
              push_result(monitor, instr, result);
              ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
              temp->previous = R2U2_TNT_TRUE | result;
              error_cond = R2U2_OK;
              break;
            }
          }
        } else {
          if (!(temp->edge & R2U2_TNT_TRUE) || (temp->edge & R2U2_TNT_TIME) <= sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->upper_bound) && (temp->previous & R2U2_TNT_TIME) >= temp->upper_bound){
            ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
            if ((op1 & R2U2_TNT_TIME) >= sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->lower_bound)){
              result = ((op1 & R2U2_TNT_TIME) + temp->lower_bound) | R2U2_TNT_FALSE;
              if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
              (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
                R2U2_DEBUG_PRINT("\tRight Op never true from [i-ub,i-lb]\n");
                push_result(monitor, instr, result);
                ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
                temp->previous = R2U2_TNT_TRUE | result;
                error_cond = R2U2_OK;
                break;
              }
            }
          }
          if (op0_rdy && !(op0 & R2U2_TNT_TRUE)){
            ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
            if ((op1 & R2U2_TNT_TIME) >= sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->lower_bound)){
              result = ((op1 & R2U2_TNT_TIME) + temp->lower_bound) | R2U2_TNT_FALSE;
              if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
              (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
                R2U2_DEBUG_PRINT("\tBoth False\n");
                push_result(monitor, instr, result);
                ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
                temp->previous = R2U2_TNT_TRUE | result;
                error_cond = R2U2_OK;
                break;
              }
            }
          }
        }
      }
      if (op0_rdy && (op0 & R2U2_TNT_TRUE) && \
        (op0 & R2U2_TNT_TIME) >= sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->lower_bound) && (temp->edge & R2U2_TNT_TRUE) && \
        ((temp->edge & R2U2_TNT_TIME) > sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->upper_bound) || (temp->previous & R2U2_TNT_TIME) < temp->upper_bound)) {
        result = min((op0 & R2U2_TNT_TIME) + temp->lower_bound, (temp->edge & R2U2_TNT_TIME) + temp->upper_bound) | R2U2_TNT_TRUE;
          if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
            (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
              R2U2_DEBUG_PRINT("\tLeft Op True Since Right Op True\n");
              r2u2_time next = max(ctrl->next_time, sub_min_zero((result & R2U2_TNT_TIME), temp->upper_bound) + 1);
              push_result(monitor, instr, result);
              ctrl->next_time = next;
              temp->previous = R2U2_TNT_TRUE | result;
              error_cond = R2U2_OK;
              break;
          }
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_TRIGGER: {
      R2U2_DEBUG_PRINT("\tPT TRIGGER\n");
      temp = &(ctrl->temporal_block);
      if (!(temp->previous & R2U2_TNT_TRUE) && (temp->previous & R2U2_TNT_TIME) < temp->lower_bound){
        R2U2_DEBUG_PRINT("Not enough data to evaluate at beginning of trace");
        result = (temp->lower_bound - 1) | R2U2_TNT_TRUE;
        push_result(monitor, instr, result);
        ctrl->next_time = 0;
        temp->previous = R2U2_TNT_TRUE | result;
        error_cond = R2U2_OK;
        break;
      }

      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      if (op1_rdy) {
        if (!(op1 & R2U2_TNT_TRUE)) {
          R2U2_DEBUG_PRINT("\tRight Op False\n");
          temp->edge = (op1 & R2U2_TNT_TIME) | R2U2_TNT_TRUE;
          ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
          if ((op1 & R2U2_TNT_TIME) >= sub_min_zero((temp->previous & R2U2_TNT_TIME), (temp->lower_bound))){
            result = ((op1 & R2U2_TNT_TIME) + temp->lower_bound) | R2U2_TNT_FALSE;
            // To handle startup behavior, the truth bit of the previous result
            // storage is used to flag that an ouput has been produced, which can
            // differentiate between a value of 0 for no output vs output produced.
            // Note: Since only the timestamp of the previous result is ever checked,
            // this overloading of the truth bit doesn't cause confict with other logic 
            // and preserves startup behavior.
            if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
            (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
              push_result(monitor, instr, result);
              ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
              temp->previous = R2U2_TNT_TRUE | result;
              error_cond = R2U2_OK;
              break;
            }
          }
        } else {
          if (!(temp->edge & R2U2_TNT_TRUE) || (temp->edge & R2U2_TNT_TIME) <= sub_min_zero((temp->previous & R2U2_TNT_TIME),temp->upper_bound) && (temp->previous & R2U2_TNT_TIME) >= temp->upper_bound){
            ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
            if ((op1 & R2U2_TNT_TIME) >= sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->lower_bound)){
              result = ((op1 & R2U2_TNT_TIME) + temp->lower_bound) | R2U2_TNT_TRUE;
              if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
              (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
                R2U2_DEBUG_PRINT("\tRight Op true from [i-ub,i-lb]\n");
                push_result(monitor, instr, result);
                ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
                temp->previous = R2U2_TNT_TRUE | result;
                error_cond = R2U2_OK;
                break;
              }
            }
          }
          if (op0_rdy && (op0 & R2U2_TNT_TRUE)){
            ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
            if ((op1 & R2U2_TNT_TIME) >= sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->lower_bound)){
              result = ((op1 & R2U2_TNT_TIME) + temp->lower_bound) | R2U2_TNT_TRUE;
              if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
              (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
                R2U2_DEBUG_PRINT("\tBoth True\n");
                push_result(monitor, instr, result);
                ctrl->next_time = (op1 & R2U2_TNT_TIME) + 1;
                temp->previous = R2U2_TNT_TRUE | result;
                error_cond = R2U2_OK;
                break;
              }
            }
          }
        }
      }
      if (op0_rdy && !(op0 & R2U2_TNT_TRUE) && \
        (op0 & R2U2_TNT_TIME) >= sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->lower_bound) && (temp->edge & R2U2_TNT_TRUE) && \
        ((temp->edge & R2U2_TNT_TIME) > sub_min_zero((temp->previous & R2U2_TNT_TIME), temp->upper_bound) || (temp->previous & R2U2_TNT_TIME) < temp->upper_bound)) {
        R2U2_DEBUG_PRINT("We are here!\n");
        result = min((op0 & R2U2_TNT_TIME) + temp->lower_bound, (temp->edge & R2U2_TNT_TIME) + temp->upper_bound) | R2U2_TNT_FALSE;
        if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
            (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
              R2U2_DEBUG_PRINT("\tLeft Op False Since Right Op False\n");
              r2u2_time next = max(ctrl->next_time, sub_min_zero((result & R2U2_TNT_TIME), temp->upper_bound) + 1);
              push_result(monitor, instr, result);
              ctrl->next_time = next;
              temp->previous = R2U2_TNT_TRUE | result;
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
        push_result(monitor, instr, op0 ^ R2U2_TNT_TRUE);
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
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE), (op1 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TRUE));
        if ((op0 & R2U2_TNT_TRUE) && (op1 & R2U2_TNT_TRUE)){
          R2U2_DEBUG_PRINT("\tBoth True\n");
          push_result(monitor, instr, min((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME)) | R2U2_TNT_TRUE);
          error_cond = R2U2_OK;
          break;
        } else if (!(op0 & R2U2_TNT_TRUE) && !(op1 & R2U2_TNT_TRUE)) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          push_result(monitor, instr, max((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME)) | R2U2_TNT_FALSE);
          error_cond = R2U2_OK;
          break;
        }
      }
      if (op0_rdy && !(op0 & R2U2_TNT_TRUE)) {
        R2U2_DEBUG_PRINT("\tLeft False\n");
        push_result(monitor, instr, (op0 & R2U2_TNT_TIME) | R2U2_TNT_FALSE);
      } else if (op1_rdy && !(op1 & R2U2_TNT_TRUE)) {
        R2U2_DEBUG_PRINT("\tRight False\n");
        push_result(monitor, instr, (op1 & R2U2_TNT_TIME) | R2U2_TNT_FALSE);
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
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE), (op1 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TRUE));
        if ((op0 & R2U2_TNT_TRUE) && (op1 & R2U2_TNT_TRUE)){
          R2U2_DEBUG_PRINT("\tBoth True\n");
          push_result(monitor, instr, max((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME)) | R2U2_TNT_TRUE);
          error_cond = R2U2_OK;
          break;
        } else if (!(op0 & R2U2_TNT_TRUE) && !(op1 & R2U2_TNT_TRUE)) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          push_result(monitor, instr, min((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME)) | R2U2_TNT_FALSE);
          error_cond = R2U2_OK;
          break;
        } 
      } 
      if (op0_rdy && (op0 & R2U2_TNT_TRUE)) {
        R2U2_DEBUG_PRINT("\tLeft True\n");
        push_result(monitor, instr, (op0 & R2U2_TNT_TIME) | R2U2_TNT_TRUE);
      } else if (op1_rdy && (op1 & R2U2_TNT_TRUE)) {
        R2U2_DEBUG_PRINT("\tRight True\n");
        push_result(monitor, instr, (op1 & R2U2_TNT_TIME) | R2U2_TNT_TRUE);
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
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE), (op1 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TRUE));
        if (((op0 & R2U2_TNT_TRUE) && (op1 & R2U2_TNT_TRUE)) || \
          (!(op0 & R2U2_TNT_TRUE) && !(op1 & R2U2_TNT_TRUE))){
          R2U2_DEBUG_PRINT("\tBoth %s\n", (op0 & R2U2_TNT_TRUE) ? "T" : "F");
          push_result(monitor, instr, min((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME)) | R2U2_TNT_TRUE);
        } else {
          R2U2_DEBUG_PRINT("\t%s not equivalent to %s\n", (op0 & R2U2_TNT_TRUE) ? "T" : "F", (op1 & R2U2_TNT_TRUE) ? "T" : "F");
          push_result(monitor, instr, min((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME))| R2U2_TNT_FALSE);
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

r2u2_status_t r2u2_mltl_configure_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr){
    R2U2_DEBUG_PRINT("\tFT Configure\n");
    r2u2_scq_arena_t arena = monitor->queue_arena;
    r2u2_scq_control_block_t *ctrl = &(arena.control_blocks[instr->memory_reference]);

      switch (instr->op1_type) {
        case R2U2_FT_OP_ATOMIC: {
            ctrl->length = instr->op1_value;

            R2U2_DEBUG_PRINT("\t\tCfg SCQ %u: len = %u\n", instr->memory_reference, ctrl->length);

            /* The first queue doesn't have a previous queue to offset from and can use
            * the slot pointed to by the control block queue pointer, so if the queue id
            * is zero, we use a different offset calculation.
            */
            if (r2u2_unlikely(instr->memory_reference == 0)) {
                // First queue counts back from end of arena, inclusive
                ctrl->queue = arena.queue_mem;
            } else {
                // All subsuquent queues count back from previous queue, exclusive
                r2u2_scq_control_block_t prev_ctrl = arena.control_blocks[instr->memory_reference - 1];
                ctrl->queue = prev_ctrl.queue + prev_ctrl.length;
            }

            ctrl->queue[0] = r2u2_infinity;

            #if R2U2_DEBUG
            r2u2_scq_queue_print(arena, instr->memory_reference);
            #endif

            return R2U2_OK;
        }
        case R2U2_FT_OP_SUBFORMULA: {
          ctrl->temporal_block.lower_bound = instr->op1_value;
          ctrl->temporal_block.upper_bound = instr->op2_value;
          break;
        }
        default: {
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          break;
        }
      }

      return R2U2_OK;
}
