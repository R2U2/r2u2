#include "r2u2.h"

#include "past_time.h"

typedef enum {
    R2U2_MLTL_PT_OPRND_EDGE_NONE = 0,
    R2U2_MLTL_PT_OPRND_EDGE_FALLING,
    R2U2_MLTL_PT_OPRND_EDGE_RISING
} r2u2_mltl_pt_oprnd_edge_t;

// We can't pull this up the the MLTL level because the subformula cases are
// tense dependent.
static inline uint8_t get_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n){
    uint32_t res;
    r2u2_mltl_operand_type_t type;
    uint32_t value;

    type  = (n == 0) ? (instr->op1_type)  : (instr->op2_type);
    value = (n == 0) ? (instr->op1_value) : (instr->op2_value);

    switch (type) {
      case R2U2_FT_OP_DIRECT:
          res = value;
          break;

      case R2U2_FT_OP_ATOMIC:
          res = (*(monitor->atomic_buffer[0]))[value];
          break;

      case R2U2_FT_OP_SUBFORMULA:
          R2U2_DEBUG_PRINT("\t\t");
          res = (*(monitor->past_time_result_buffer[0]))[value];
          break;

      case R2U2_FT_OP_NOT_SET:
          res = 0;
          break;

      default:
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          res = 0;
          break;
    }

    return (uint8_t)res;
}

static inline r2u2_mltl_pt_oprnd_edge_t get_operand_edge(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {
    r2u2_bool v, v_p;
    r2u2_mltl_operand_type_t type;
    uint32_t value;

    type  = (n == 0) ? (instr->op1_type)  : (instr->op2_type);
    value = (n == 0) ? (instr->op1_value) : (instr->op2_value);

    switch (type) {
      case R2U2_FT_OP_ATOMIC:
          v = (*(monitor->atomic_buffer[0]))[value];
          v_p = (*(monitor->atomic_buffer[1]))[value];
          break;

      case R2U2_FT_OP_SUBFORMULA:
          v = (*(monitor->past_time_result_buffer[0]))[value];
          v_p = (*(monitor->past_time_result_buffer[1]))[value];
          break;

      // Literals have no edges
      case R2U2_FT_OP_DIRECT:
      case R2U2_FT_OP_NOT_SET:
          return R2U2_MLTL_PT_OPRND_EDGE_NONE;

      default:
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          return R2U2_MLTL_PT_OPRND_EDGE_NONE;
    }
    // At monitor->time_stamp = 0, we need either a rising or falling edge.
    // v determines the edge
    if (v && (!v_p || !monitor->time_stamp)) {
        return R2U2_MLTL_PT_OPRND_EDGE_RISING;
    }
    if (!v && (v_p || !monitor->time_stamp)) {
        return R2U2_MLTL_PT_OPRND_EDGE_FALLING;
    }
    return R2U2_MLTL_PT_OPRND_EDGE_NONE;
}

r2u2_status_t r2u2_mltl_pt_update(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr) {
  r2u2_status_t error_cond;
  r2u2_mltl_pt_oprnd_edge_t edge;
  r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
  r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);
  r2u2_duoq_pt_interval_t intrvl;
  r2u2_bool *res = &((*(monitor->past_time_result_buffer[0]))[instr->memory_reference]);

  // TODO(bckempa): We can split these out to static inline functions for
  // easier reading and debugging (breakpoints, stack frames, etc.)
  switch (instr->opcode) {
    case R2U2_MLTL_OP_PT_NOP: {
      R2U2_DEBUG_PRINT("\tPT[%u] NOP\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_CONFIGURE: {
      R2U2_DEBUG_PRINT("PT Configure\n");

      switch (instr->op1_type) {
        case R2U2_FT_OP_ATOMIC: {
          R2U2_DEBUG_PRINT("\tBox Queue length setup\n");
          r2u2_duoq_config(arena, instr->memory_reference, instr->op1_value, instr->op2_value);
          r2u2_duoq_pt_effective_id_set(arena, instr->memory_reference, instr->op2_value);
          break;
        }
        case R2U2_FT_OP_SUBFORMULA: {
          R2U2_DEBUG_PRINT("\tBox Queue interval setup\n");
          ctrl->next_time = instr->op1_value;
          ctrl->read2 = instr->op2_value;
          break;
        }
        default: {
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          break;
        }
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_LOAD: {
      R2U2_DEBUG_PRINT("\tPT[%u] LOAD a%d\t", instr->memory_reference, instr->op1_value);
      *res = get_operand(monitor, instr, 0);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_RETURN: {
      R2U2_DEBUG_PRINT("\tPT[%u] RETURN PT[%d] f:%d\t", instr->memory_reference, instr->op1_value, instr->op2_value);
      if (monitor->out_file != NULL) {
        fprintf(monitor->out_file, "%d:%u,%s\n",
                get_operand(monitor, instr, 1), monitor->time_stamp,
                get_operand(monitor, instr, 0) ? "T" : "F");
        R2U2_DEBUG_PRINT("= %d:%u,%s\n",
                get_operand(monitor, instr, 1), monitor->time_stamp,
                get_operand(monitor, instr, 0) ? "T" : "F");
      }

      if (monitor->out_func != NULL) {
        (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &(r2u2_verdict){monitor->time_stamp, get_operand(monitor, instr, 0)});
      }

      error_cond = R2U2_OK;
      break;
    }

    case R2U2_MLTL_OP_PT_ONCE: {
      // We use the queue to track intervals of all false values.
      // as long as the region of interest isn't entirely within this interval.
      // then the operator evaluates true

      // Temporal operator, store result at effective memory_reference from duoq
      res = &((*(monitor->past_time_result_buffer[0]))[r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference)]);
      R2U2_DEBUG_PRINT("\tPT[%u] O[%d,%d] PT[%d]\n", r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference), ctrl->next_time, ctrl->read2, instr->op1_value);

      intrvl = r2u2_duoq_pt_peek(arena, instr->memory_reference);
      if ((intrvl.end != R2U2_TNT_TRUE) && ((intrvl.end + ctrl->next_time) < monitor->time_stamp)) {
          // Garbage collection
          intrvl = r2u2_duoq_pt_tail_pop(arena, instr->memory_reference);
          R2U2_DEBUG_PRINT("\tGarbage collection, popping interval [%d, %d]\n", intrvl.start, intrvl.end);
      }

      // for falling edge
      edge = get_operand_edge(monitor, instr, 0);
      if (edge == R2U2_MLTL_PT_OPRND_EDGE_FALLING) {
          R2U2_DEBUG_PRINT("\tFalling edge detected, pushing to queue\n");
          r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){monitor->time_stamp, R2U2_TNT_TRUE});
      } else if ((edge == R2U2_MLTL_PT_OPRND_EDGE_RISING) && !r2u2_duoq_pt_is_empty(arena, instr->memory_reference)) {
          R2U2_DEBUG_PRINT("\tRising edge detected, closing interval\n");
          intrvl = r2u2_duoq_pt_head_pop(arena, instr->memory_reference);
          r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){intrvl.start, monitor->time_stamp - 1});
          // TODO(bckempa): Verify and re-enable this optimization - don't store intervals that will never be true
          // if(((monitor->time_stamp + ctrl->next_time) >= (intrvl.start + ctrl->read2 + 1)) && ((monitor->time_stamp == 0) || (ctrl->next_time >= 1))){
          //     //R2U2_DEBUG_PRINT("***** Feasibility Check *****\n");
          //     r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){intrvl.start, monitor->time_stamp - 1});
          // }
      }

      // Since this logic is identical to the historically operator, we use the
      // same conditionals before inverting the result

      intrvl = r2u2_duoq_pt_peek(arena, instr->memory_reference);

      if (ctrl->next_time > monitor->time_stamp) {
        // Insufficient data, true by definition
        R2U2_DEBUG_PRINT("\t  Startup behavior: t < lower bound\n");
        *res = true;
      } else if (intrvl.start != R2U2_TNT_TRUE) {
        R2U2_DEBUG_PRINT("\tChecking interval start\n");
        if (ctrl->read2 > monitor->time_stamp) {
            R2U2_DEBUG_PRINT("\t  Partial interval check: (%d == 0) = %c\n", intrvl.start, (intrvl.start == 0)?'T':'F');
            *res = intrvl.start == 0;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d <= %d) = %c\n", intrvl.start, ctrl->read2, monitor->time_stamp, (intrvl.start + ctrl->read2 <= monitor->time_stamp)?'T':'F');
            *res = intrvl.start + ctrl->read2 <= monitor->time_stamp;
        }

        R2U2_DEBUG_PRINT("\tChecking interval end:\n");
        if (intrvl.end == R2U2_TNT_TRUE) {
            R2U2_DEBUG_PRINT("\t  Open interval: T\n");
            *res &= true;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d >= %d) = %c\n", intrvl.end, ctrl->next_time, monitor->time_stamp, (intrvl.end + ctrl->next_time >= monitor->time_stamp)?'T':'F');
            *res &= intrvl.end + ctrl->next_time >= monitor->time_stamp;
        }
      } else {
        R2U2_DEBUG_PRINT("\tNo interval to check\n");
        *res = false;
      }

      *res = !*res;
      R2U2_DEBUG_PRINT("\tPT[%u] = %d\n", r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference), *res);

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_HISTORICALLY: {
      // Temporal operator, store result at effective memory_reference from duoq
      res = &((*(monitor->past_time_result_buffer[0]))[r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference)]);
      R2U2_DEBUG_PRINT("\tPT[%u] H[%d,%d] PT[%d]\n", r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference), ctrl->next_time, ctrl->read2, instr->op1_value);
      intrvl = r2u2_duoq_pt_peek(arena, instr->memory_reference);
      if ((intrvl.end != R2U2_TNT_TRUE) && (intrvl.end + ctrl->next_time) < monitor->time_stamp) {
          intrvl = r2u2_duoq_pt_tail_pop(arena, instr->memory_reference);
          R2U2_DEBUG_PRINT("\tGarbage collection, popping interval [%d, %d]\n", intrvl.start, intrvl.end);
      }

      edge = get_operand_edge(monitor, instr, 0);
      if (edge == R2U2_MLTL_PT_OPRND_EDGE_RISING) {
          // Start new open interval on rising edge
          R2U2_DEBUG_PRINT("\tRising edge detected, pushing to queue\n");
          r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){monitor->time_stamp, R2U2_TNT_TRUE});
      }
      else if ((edge == R2U2_MLTL_PT_OPRND_EDGE_FALLING) && !r2u2_duoq_pt_is_empty(arena, instr->memory_reference)) {
          // Here we can close the interval
          // However, as an optimization, we discard infeasible intervals
          R2U2_DEBUG_PRINT("\tFalling edge detected, closing interval\n");
          intrvl = r2u2_duoq_pt_head_pop(arena, instr->memory_reference);
          r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){intrvl.start, monitor->time_stamp - 1});
          // TODO(bckempa): Verify and re-enable this optimization - don't store intervals that will never be true
          // if(((monitor->time_stamp + ctrl->next_time) >= (intrvl.start + ctrl->read2 + 1)) && ((monitor->time_stamp == 0) || (ctrl->next_time >= 1))){
          //     r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){intrvl.start, monitor->time_stamp - 1});
          //     R2U2_DEBUG_PRINT("\t\tAdding valid interval to queue: [%d, %d]\n", intrvl.start, monitor->time_stamp - 1);
          // }
      }

      intrvl = r2u2_duoq_pt_peek(arena, instr->memory_reference);

      if (ctrl->next_time > monitor->time_stamp) {
        // Insufficient data, true by definition
        R2U2_DEBUG_PRINT("\t  Startup behavior: t < lower bound\n");
        *res = true;
      } else if (intrvl.start != R2U2_TNT_TRUE) {
        R2U2_DEBUG_PRINT("\tChecking interval start\n");
        if (ctrl->read2 > monitor->time_stamp) {
            R2U2_DEBUG_PRINT("\t  Partial interval check: (%d == 0) = %c\n", intrvl.start, (intrvl.start == 0)?'T':'F');
            *res = intrvl.start == 0;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d <= %d) = %c\n", intrvl.start, ctrl->read2, monitor->time_stamp, (intrvl.start + ctrl->read2 <= monitor->time_stamp)?'T':'F');
            *res = intrvl.start + ctrl->read2 <= monitor->time_stamp;
        }

        R2U2_DEBUG_PRINT("\tChecking interval end:\n");
        if (intrvl.end == R2U2_TNT_TRUE) {
            R2U2_DEBUG_PRINT("\t  Open interval: T\n");
            *res &= true;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d >= %d) = %c\n", intrvl.end, ctrl->next_time, monitor->time_stamp, (intrvl.end + ctrl->next_time >= monitor->time_stamp)?'T':'F');
            *res &= intrvl.end + ctrl->next_time >= monitor->time_stamp;
        }
      } else {
        R2U2_DEBUG_PRINT("\tNo interval to check\n");
        *res = false;
      }

      R2U2_DEBUG_PRINT("\tPT[%u] = %d\n", r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference), *res);

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_SINCE: {
      // Works similar to Once, but with additional reset logic when

      // Temporal operator, store result at effective memory_reference from duoq
      res = &((*(monitor->past_time_result_buffer[0]))[r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference)]);
      R2U2_DEBUG_PRINT("\tPT[%u] S[%d,%d] PT[%d] PT[%d]\n", r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference), ctrl->next_time, ctrl->read2, instr->op1_value, instr->op2_value);
      intrvl = r2u2_duoq_pt_peek(arena, instr->memory_reference);
      if ((intrvl.end != R2U2_TNT_TRUE) && (intrvl.end + ctrl->next_time) < monitor->time_stamp) {
          intrvl = r2u2_duoq_pt_tail_pop(arena, instr->memory_reference);
          R2U2_DEBUG_PRINT("\tGarbage collection, popping interval [%d, %d]\n", intrvl.start, intrvl.end);
      }

      if (get_operand(monitor, instr, 0)) {
          R2U2_DEBUG_PRINT("\tLeft operand holds, testing right operand edge\n");
          edge = get_operand_edge(monitor, instr, 1);
          if (edge == R2U2_MLTL_PT_OPRND_EDGE_FALLING) {
              R2U2_DEBUG_PRINT("\tFalling edge detected on right operand, pushing to queue\n");
              r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){monitor->time_stamp, R2U2_TNT_TRUE});
          } else if ((edge == R2U2_MLTL_PT_OPRND_EDGE_RISING) && !r2u2_duoq_pt_is_empty(arena, instr->memory_reference)) {
              R2U2_DEBUG_PRINT("\tRising edge detected on right operand, closing interval\n");
              intrvl = r2u2_duoq_pt_head_pop(arena, instr->memory_reference);
              r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){intrvl.start, monitor->time_stamp - 1});
              // TODO(bckempa): Verify and re-enable this optimization - don't store intervals that will never be true
              // if(((monitor->time_stamp + ctrl->next_time) >= (intrvl.start + ctrl->read2 + 1)) && ((monitor->time_stamp == 0) || (ctrl->next_time >= 1))){
              //     r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){intrvl.start, monitor->time_stamp - 1});
              // }
          }
      } else { // p1 does not hold
          R2U2_DEBUG_PRINT("\tLeft operand false, resetting based on right operand\n");
          if (get_operand(monitor, instr, 1)) {
              R2U2_DEBUG_PRINT("\tRight operand holds, setting queue\n");
              r2u2_duoq_pt_reset(arena, instr->memory_reference);
              if (monitor->time_stamp != 0) {
                r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){0, monitor->time_stamp - 1});
              }
          } else {
              R2U2_DEBUG_PRINT("\tRight operand false, resetting queue\n");
              intrvl = r2u2_duoq_pt_tail_pop(arena, instr->memory_reference);
              r2u2_duoq_pt_push(arena, instr->memory_reference, (r2u2_duoq_pt_interval_t){0, R2U2_TNT_TRUE});
          }
      }
      intrvl = r2u2_duoq_pt_peek(arena, instr->memory_reference);

      if (ctrl->next_time > monitor->time_stamp) {
        // Insufficient data, true by definition
        R2U2_DEBUG_PRINT("\t  Startup behavior: t < lower bound\n");
        *res = true;
      } else if (intrvl.start != R2U2_TNT_TRUE) {
        R2U2_DEBUG_PRINT("\tChecking interval start\n");
        if (ctrl->read2 > monitor->time_stamp) {
            R2U2_DEBUG_PRINT("\t  Partial interval check: (%d == 0) = %c\n", intrvl.start, (intrvl.start == 0)?'T':'F');
            *res = intrvl.start == 0;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d <= %d) = %c\n", intrvl.start, ctrl->read2, monitor->time_stamp, (intrvl.start + ctrl->read2 <= monitor->time_stamp)?'T':'F');
            *res = intrvl.start + ctrl->read2 <= monitor->time_stamp;
        }

        R2U2_DEBUG_PRINT("\tChecking interval end:\n");
        if (intrvl.end == R2U2_TNT_TRUE) {
            R2U2_DEBUG_PRINT("\t  Open interval: T\n");
            *res &= true;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d >= %d) = %c\n", intrvl.end, ctrl->next_time, monitor->time_stamp, (intrvl.end + ctrl->next_time >= monitor->time_stamp)?'T':'F');
            *res &= intrvl.end + ctrl->next_time >= monitor->time_stamp;
        }
      } else {
        R2U2_DEBUG_PRINT("\tNo interval to check\n");
        *res = false;
      }

      *res = !*res;
      R2U2_DEBUG_PRINT("\tPT[%u] = %d\n", r2u2_duoq_pt_effective_id_get(arena, instr->memory_reference), *res);

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_LOCK: {
      R2U2_DEBUG_PRINT("\tPT[%u] LOCK\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }

    case R2U2_MLTL_OP_PT_NOT: {
      R2U2_DEBUG_PRINT("\tPT[%u] NOT PT[%d]\t", instr->memory_reference, instr->op1_value);
      *res = !get_operand(monitor, instr, 0);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_AND: {
      R2U2_DEBUG_PRINT("\tPT[%u] AND PT[%d] PT[%d]\t", instr->memory_reference, instr->op1_value, instr->op2_value);
      *res = get_operand(monitor, instr, 0) && get_operand(monitor, instr, 1);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_OR: {
      R2U2_DEBUG_PRINT("\tPT[%u] OR PT[%d]\t", instr->memory_reference, instr->op1_value);
      *res = get_operand(monitor, instr, 0) || get_operand(monitor, instr, 1);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_IMPLIES: {
      R2U2_DEBUG_PRINT("\tPT[%u] IMPLIES PT[%d] PT[%d]\t", instr->memory_reference, instr->op1_value, instr->op2_value);
      *res = (!get_operand(monitor, instr, 0)) || get_operand(monitor, instr, 1);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }

    case R2U2_MLTL_OP_PT_NAND: {
      R2U2_DEBUG_PRINT("\tPT[%u] NAND\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_NOR: {
      R2U2_DEBUG_PRINT("\tPT[%u] NOR\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_XOR: {
      R2U2_DEBUG_PRINT("\tPT[%u] XOR\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_EQUIVALENT: {
      R2U2_DEBUG_PRINT("\tPT[%u] EQUIVALENT PT[%d] PT[%d]\t", instr->memory_reference, instr->op1_value, instr->op2_value);
      *res = (get_operand(monitor, instr, 0) == get_operand(monitor, instr, 1));
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    default: {
      // Somehow got into wrong tense dispatch
      R2U2_DEBUG_PRINT("Warning: Bad Inst Type\n");
      error_cond = R2U2_INVALID_INST;
      break;
    }
  }

  return error_cond;
}
