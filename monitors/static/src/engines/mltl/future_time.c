#include "r2u2.h"

#include "future_time.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))

/// @brief      Check for and retrieve an instruction operand's next value
/// @param[in]  monitor A pointer to the R2U2 monitor
/// @param[in]  instr A pointer to the instruction
/// @param[in]  n Operand to check, 0 for left/first, anything else for right
/// @param[out] result The operand TnT - only vaid if return value is true
/// @return     Boolean indicating if data is ready and `result` is valid
static r2u2_bool check_operand_data(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_bool op_num, r2u2_tnt_t *result) {
    r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
    r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);
    r2u2_tnt_t *rd_ptr; // Hold off on this in case it doesn't exist...

    // Get operand info based on `n` which indicates left/first v.s. right/second
    r2u2_mltl_operand_type_t op_type = (op_num == 0) ? (instr->op1_type) : (instr->op2_type);
    uint32_t value = (op_num == 0) ? (instr->op1_value) : (instr->op2_value);

    switch (op_type) {

      case R2U2_FT_OP_DIRECT:
        *result = monitor->time_stamp | ((value) ? R2U2_TNT_TRUE : R2U2_TNT_FALSE);
        return true;

      case R2U2_FT_OP_ATOMIC:
        // Only load in atomics on first loop of time step
        // TODO(bckempa) This might remove the need for load...
        #if R2U2_DEBUG
          // TODO(bckempa) Add check for discarded top bit in timestamp
        #endif
        // Assuming the cost of the bitops is cheaper than an if branch
        *result = monitor->time_stamp | (((*(monitor->atomic_buffer[0]))[value]) ? R2U2_TNT_TRUE : R2U2_TNT_FALSE);
        return (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP);

      case R2U2_FT_OP_SUBFORMULA:
        // Handled by the duo queue check function, just need the arguments
        rd_ptr = (op_num == 0) ? &(ctrl->read1) : &(ctrl->read2);

        return r2u2_duoq_ft_check(arena, value, rd_ptr, ctrl->next_time, result);

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
  r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
  r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);

  r2u2_duoq_ft_write(arena, instr->memory_reference, result);
  R2U2_DEBUG_PRINT("\t(%d,%s)\n", result & R2U2_TNT_TIME, (result & R2U2_TNT_TRUE) ? "T" : "F" );

  ctrl->next_time = (result & R2U2_TNT_TIME)+1;

  // TODO(bckempa): Inline or macro this
  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

  return R2U2_OK;
}

r2u2_status_t r2u2_mltl_ft_update(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr) {

  r2u2_bool op0_rdy, op1_rdy;
  r2u2_tnt_t op0, op1, result;
  r2u2_status_t error_cond;

  r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
  r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);
  r2u2_duoq_temporal_block_t *temp; // Only set this if using a temporal op

  switch (instr->opcode) {

    /* Control Commands */
    case R2U2_MLTL_OP_FT_NOP: {
      R2U2_DEBUG_PRINT("\tFT NOP\n");
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_CONFIGURE: {
      R2U2_DEBUG_PRINT("\tFT Configure\n");

      switch (instr->op1_type) {
        case R2U2_FT_OP_ATOMIC: {
          r2u2_duoq_config(arena, instr->memory_reference, instr->op1_value);
          break;
        }
        case R2U2_FT_OP_SUBFORMULA: {
          r2u2_duoq_ft_temporal_config(arena, instr->memory_reference);
          temp = r2u2_duoq_ft_temporal_get(arena, instr->memory_reference);
          temp->lower_bound = instr->op1_value;
          temp->upper_bound = instr->op2_value;
          break;
        }
        default: {
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          break;
        }
      }


          // // Rise/Fall edge detection initialization
          // switch (instr->opcode) {
          //   case R2U2_MLTL_OP_FT_GLOBALLY:
          //       temp->previous = (r2u2_verdict) {r2u2_infinity, false};
          //       break;
          //   case R2U2_MLTL_OP_FT_UNTIL:
          //       temp->previous = (r2u2_verdict) {r2u2_infinity, true};
          //       break;
          //   default:
          //       temp->previous = (r2u2_verdict) {0, true};
          // }


      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_LOAD: {
      R2U2_DEBUG_PRINT("\tFT LOAD\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        push_result(monitor, instr, op0);
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_RETURN: {
      R2U2_DEBUG_PRINT("\tFT RETURN\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        R2U2_DEBUG_PRINT("\t(%d,%s)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE) ? "T" : "F");

        // The bookkeeping of tau and progress noramlly happen in `push_result`
        // so we have to handle that manually here since return doesn't push
        ctrl->next_time = (op0 & R2U2_TNT_TIME)+1;

        if (monitor->out_file != NULL) {
          fprintf(monitor->out_file, "%d:%u,%s\n", instr->op2_value, (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE) ? "T" : "F");
        }

        if (monitor->out_func != NULL) {
          // TODO(bckempa): Migrate external function pointer interface to use r2u2_tnt_t
          (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &((r2u2_verdict){op0 & R2U2_TNT_TIME, (op0 & R2U2_TNT_TRUE) ? true : false}));
        }

        if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

      }

      error_cond = R2U2_OK;
      break;
    }

    /* Future Temporal Observers */
    case R2U2_MLTL_OP_FT_EVENTUALLY: {
      R2U2_DEBUG_PRINT("\tFT EVENTUALLY\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_FT_GLOBALLY: {
      R2U2_DEBUG_PRINT("\tFT GLOBALLY\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        R2U2_DEBUG_PRINT("\tGot data\n");
        temp = r2u2_duoq_ft_temporal_get(arena, instr->memory_reference);

        // verdict compaction aware rising edge detection
        // To avoid reserving a null, sentinal, or "infinity" timestamp, we
        // also have to check for satarting conditions.
        // TODO(bckempa): There must be a better way, is it cheaper to count?
        if((op0 & R2U2_TNT_TRUE) && !(temp->previous & R2U2_TNT_TRUE)) {
          if (ctrl->next_time != 0) {
            temp->edge = (temp->previous | R2U2_TNT_TRUE) + 1;
          } else {
            temp->edge = R2U2_TNT_TRUE;
          }
          R2U2_DEBUG_PRINT("\tRising edge at t= %d\n", (temp->edge & R2U2_TNT_TIME));
        }

        if ((op0 & R2U2_TNT_TRUE) && (temp->edge >= R2U2_TNT_TRUE) && ((op0 & R2U2_TNT_TIME) >= temp->upper_bound - temp->lower_bound + (temp->edge & R2U2_TNT_TIME)) && ((op0 & R2U2_TNT_TIME) >= temp->upper_bound)) {
          R2U2_DEBUG_PRINT("\tPassed\n");
          push_result(monitor, instr, ((op0 & R2U2_TNT_TIME) - temp->upper_bound) | R2U2_TNT_TRUE);
        } else if (!(op0 & R2U2_TNT_TRUE) && ((op0 & R2U2_TNT_TIME) >= temp->lower_bound)) {
          R2U2_DEBUG_PRINT("\tFailed\n");
          push_result(monitor, instr, ((op0 & R2U2_TNT_TIME) - temp->lower_bound) | R2U2_TNT_FALSE);
        } else {
          R2U2_DEBUG_PRINT("\tWaiting...\n");
        }

        // We only need to see each timestep once, regaurdless of outcome
        ctrl->next_time = (op0 & R2U2_TNT_TIME)+1;
        temp->previous = op0;
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_UNTIL: {
      R2U2_DEBUG_PRINT("\tFT UNTIL\n");

      if (check_operand_data(monitor, instr, 0, &op0) && check_operand_data(monitor, instr, 1, &op1)) {
        temp = r2u2_duoq_ft_temporal_get(arena, instr->memory_reference);

        // We need to see every timesetp as an (op0, op1) pair
        r2u2_time tau = min(op0 & R2U2_TNT_TIME, op1 & R2U2_TNT_TIME);
        ctrl->next_time = tau+1;

        if(op1 & R2U2_TNT_TRUE) {temp->edge = op1 & R2U2_TNT_TIME;}
        R2U2_DEBUG_PRINT("\tTime since right operand high: %d\n", tau - temp->edge);

        if ((op1 & R2U2_TNT_TRUE) && (tau >= (temp->previous & R2U2_TNT_TIME) + temp->lower_bound)) {
          R2U2_DEBUG_PRINT("\tRight Op True\n");
          result = (tau - temp->lower_bound) | R2U2_TNT_TRUE;
        } else if (!(op0 & R2U2_TNT_TRUE) && (tau >= (temp->previous & R2U2_TNT_TIME) + temp->lower_bound)) {
          R2U2_DEBUG_PRINT("\tLeft Op False\n");
          result = (tau - temp->lower_bound) | R2U2_TNT_FALSE;
        } else if ((tau >= temp->upper_bound - temp->lower_bound + temp->edge) && (tau >= (temp->previous & R2U2_TNT_TIME) + temp->upper_bound)) {
          R2U2_DEBUG_PRINT("\tTime Elapsed\n");
          result = (tau - temp->upper_bound) | R2U2_TNT_FALSE;
        } else {
          /* Still waiting, return early */
          error_cond = R2U2_OK;
          break;
        }

        // Didn't hit the else case above means we a result. If it is new, that
        // is the timestamp is grater than the one in temp->previous, we push.
        // We don't want to reset desired_time_stamp based on the result
        // so we reset `next_time` after we push to avoid one-off return logic
        if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
            (((result & R2U2_TNT_TIME) == 0) && (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP))) {
          push_result(monitor, instr, result);
          ctrl->next_time = tau+1;
        }
        // TODO(bckempa): Should this be in the above block? Does it matter?
        temp->previous = result;
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_RELEASE: {
      R2U2_DEBUG_PRINT("\tFT RELEASE\n");
      error_cond = R2U2_UNIMPL;
      break;
    }

    /* Propositional Logic Observers */
    case R2U2_MLTL_OP_FT_NOT: {
      R2U2_DEBUG_PRINT("\tFT NOT\n");

      if (check_operand_data(monitor, instr, 0, &op0)) {
        push_result(monitor, instr, op0 ^ R2U2_TNT_TRUE);
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_AND: {
      R2U2_DEBUG_PRINT("\tFT AND\n");

      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (op0_rdy && op1_rdy) {
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE), (op1 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TRUE));
        if ((op0 & R2U2_TNT_TRUE) && (op1 & R2U2_TNT_TRUE)){
          R2U2_DEBUG_PRINT("\tBoth True\n");
          push_result(monitor, instr, min((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME)) | R2U2_TNT_TRUE);
        } else if (!(op0 & R2U2_TNT_TRUE) && !(op1 & R2U2_TNT_TRUE)) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          push_result(monitor, instr, max((op0 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TIME))| R2U2_TNT_FALSE);
        } else if (op0 & R2U2_TNT_TRUE) {
          R2U2_DEBUG_PRINT("\tOnly Left True\n");
          push_result(monitor, instr, (op1 & R2U2_TNT_TIME)| R2U2_TNT_FALSE);
        } else {
          R2U2_DEBUG_PRINT("\tOnly Right True\n");
          push_result(monitor, instr, (op0 & R2U2_TNT_TIME)| R2U2_TNT_FALSE);
        }
      } else if (op0_rdy) {
        R2U2_DEBUG_PRINT("\tOnly Left Ready: (%d, %d)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE));
        if(!(op0 & R2U2_TNT_TRUE)) {
          push_result(monitor, instr, (op0 & R2U2_TNT_TIME)| R2U2_TNT_FALSE);
        }
      } else if (op1_rdy) {
        R2U2_DEBUG_PRINT("\tOnly Right Ready: (%d, %d)\n", (op1 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TRUE));
        if(!(op1 & R2U2_TNT_TRUE)) {
          push_result(monitor, instr, (op1 & R2U2_TNT_TIME) | R2U2_TNT_FALSE);
        }
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_OR: {
      R2U2_DEBUG_PRINT("\tFT OR\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_FT_IMPLIES: {
      R2U2_DEBUG_PRINT("\tFT IMPLIES\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_FT_NAND: {
      R2U2_DEBUG_PRINT("\tFT NAND\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_FT_NOR: {
      R2U2_DEBUG_PRINT("\tFT NOR\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_FT_XOR: {
      R2U2_DEBUG_PRINT("\tFT XOR\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_FT_EQUIVALENT: {
      R2U2_DEBUG_PRINT("\tFT EQUIVALENT\n");
      error_cond = R2U2_UNIMPL;
      break;
    }

    /* Error Case */
    default: {
      // Somehow got into wrong tense dispatch
      R2U2_DEBUG_PRINT("Warning: Bad Inst Type\n");
      error_cond = R2U2_INVALID_INST;
      break;
    }
  }

  return error_cond;
}
