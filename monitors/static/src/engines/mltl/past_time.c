#include "r2u2.h"

#include "past_time.h"

typedef enum {
    R2U2_MLTL_PT_OPRND_EDGE_NONE = 0,
    R2U2_MLTL_PT_OPRND_EDGE_FALLING,
    R2U2_MLTL_PT_OPRND_EDGE_RISING
} r2u2_mltl_pt_oprnd_edge_t;

r2u2_mltl_pt_oprnd_edge_t get_operand_edge(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n);


static uint8_t get_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {
    uint8_t res;
    r2u2_mltl_operand_t *op;

    #if R2U2_DEBUG
      // TODO(bckempa): Debug build bounds checking
      // assert();
    #endif
    if (n == 0) {
      op = &(instr->op1);
    } else {
      op = &(instr->op2);
    }

    switch (op->opnd_type) {
      case R2U2_FT_OP_DIRECT:
          res = op->value;
          break;

      case R2U2_FT_OP_ATOMIC:
          res = (*(monitor->atomic_buffer[0]))[op->value];
          break;

      case R2U2_FT_OP_SUBFORMULA:
          res = (*(monitor->past_time_result_buffer[0]))[op->value];
          break;

      case R2U2_FT_OP_NOT_SET:
          res = 0;
          break;
    }

    return res;
}

r2u2_mltl_pt_oprnd_edge_t get_operand_edge(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {
    r2u2_bool v, v_p;
    r2u2_mltl_operand_t *op;

    if (n == 0) {
      op = &(instr->op1);
    } else {
      op = &(instr->op2);
    }

    switch (op->opnd_type) {
      case R2U2_FT_OP_ATOMIC:
          v = (*(monitor->atomic_buffer[0]))[op->value];
          v_p = (*(monitor->atomic_buffer[1]))[op->value];
          break;

      case R2U2_FT_OP_SUBFORMULA:
          v = (*(monitor->past_time_result_buffer[0]))[op->value];
          v_p = (*(monitor->past_time_result_buffer[1]))[op->value];
          break;

      // Literals have no edges
      case R2U2_FT_OP_DIRECT:
      case R2U2_FT_OP_NOT_SET:
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
  r2u2_boxq_t *boxq;
  r2u2_boxq_intvl_t intrvl;
  r2u2_bool *res = &((*(monitor->past_time_result_buffer[0]))[instr->memory_reference]);

  // TODO(bckempa): We can split these out to static inline functions for
  // easier reading and debugging (breakpoints, stack frames, etc.)
  switch (instr->opcode) {
    case R2U2_MLTL_OP_PT_NOP: {
      R2U2_DEBUG_PRINT("\tPT[%zu] NOP\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_CONFIGURE: {
      R2U2_DEBUG_PRINT("PT Configure\n");

      boxq = &(((r2u2_boxq_t*)(*(monitor->past_time_queue_mem)))[instr->op1.value]);

      switch (instr->op2.opnd_type) {
        case R2U2_FT_OP_DIRECT: {
          R2U2_DEBUG_PRINT("\tBox Queue setup\n");
          // Encodes box queue info; op[1] is length, mem_ref is offset
          r2u2_boxq_reset(boxq);
          boxq->length = get_operand(monitor, instr, 1);
          r2u2_boxq_intvl_t *elements = ((r2u2_boxq_intvl_t*)(*(monitor->past_time_queue_mem)));
          // TODO(bckempa): need better sizing of array extents when switch elements
          boxq->queue = &(elements[(R2U2_MAX_BOXQ_BYTES / sizeof(r2u2_boxq_intvl_t)) - instr->memory_reference]);
          break;
        }
        case R2U2_FT_OP_ATOMIC: {
          // Encodes interval in mem_ref; op[1] is low (0) or high (1) bound
          if (instr->op2.value) {
            R2U2_DEBUG_PRINT("\tHigh interval setup\n");
            boxq->interval.end = (r2u2_time) instr->memory_reference;
            R2U2_DEBUG_PRINT("\tPT[%d] [%d,%d]\n", instr->op1.value, boxq->interval.start, boxq->interval.end);
          } else {
            R2U2_DEBUG_PRINT("\tLow interval setup\n");
            boxq->interval.start = (r2u2_time) instr->memory_reference;
            R2U2_DEBUG_PRINT("\tPT[%d] [%d,%d]\n", instr->op1.value, boxq->interval.start, boxq->interval.end);
          }
          break;
        }
        default: {
          break;
        }
      }


      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_LOAD: {
      R2U2_DEBUG_PRINT("\tPT[%zu] LOAD a%d\t", instr->memory_reference, instr->op1.value);
      *res = get_operand(monitor, instr, 0);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_RETURN: {
      R2U2_DEBUG_PRINT("\tPT[%zu] RETURN PT[%d] f:%d\t", instr->memory_reference, instr->op1.value, instr->op2.value);
      if (monitor->out_file != NULL) {
        fprintf(monitor->out_file, "%d:%u,%s\n",
                get_operand(monitor, instr, 1), monitor->time_stamp,
                get_operand(monitor, instr, 0) ? "T" : "F");
        R2U2_DEBUG_PRINT("= %d:%u,%s\n",
                get_operand(monitor, instr, 1), monitor->time_stamp,
                get_operand(monitor, instr, 0) ? "T" : "F");
      }

      if (monitor->out_func != NULL) {
        (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &(r2u2_verdict){get_operand(monitor, instr, 0), monitor->time_stamp});
      }

      error_cond = R2U2_OK;
      break;
    }

    case R2U2_MLTL_OP_PT_ONCE: {
      // We use the queue to track intervals of all false values.
      // as long as the region of interest isn't entirely within this interval.
      // then the operator evaluates true
      boxq = &(((r2u2_boxq_t*)(*(monitor->past_time_queue_mem)))[instr->memory_reference]);
      R2U2_DEBUG_PRINT("\tPT[%zu] O[%d,%d] PT[%d]\n", instr->memory_reference, boxq->interval.start, boxq->interval.end, instr->op1.value);

      intrvl = r2u2_boxq_peek(boxq);
      if ((intrvl.end != r2u2_infinity) && ((intrvl.end + boxq->interval.start) < monitor->time_stamp)) {
          // Garbage collection
          intrvl = r2u2_boxq_pop_tail(boxq);
          R2U2_DEBUG_PRINT("\tGarbage collection, popping interval [%d, %d]\n", intrvl.start, intrvl.end);
      }

      // for falling edge
      edge = get_operand_edge(monitor, instr, 0);
      if (edge == R2U2_MLTL_PT_OPRND_EDGE_FALLING) {
          R2U2_DEBUG_PRINT("\tFalling edge detected, pushing to queue\n");
          r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){monitor->time_stamp, r2u2_infinity});
      } else if ((edge == R2U2_MLTL_PT_OPRND_EDGE_RISING) && !r2u2_boxq_is_empty(boxq)) {
          R2U2_DEBUG_PRINT("\tRising edge detected, closing interval\n");
          intrvl = r2u2_boxq_pop_head(boxq);
          r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){intrvl.start, monitor->time_stamp - 1});
          // TODO(bckempa): Verify and re-enable this optimization - don't store intervals that will never be true
          // if(((monitor->time_stamp + boxq->interval.start) >= (intrvl.start + boxq->interval.end + 1)) && ((monitor->time_stamp == 0) || (boxq->interval.start >= 1))){
          //     //R2U2_DEBUG_PRINT("***** Feasibility Check *****\n");
          //     r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){intrvl.start, monitor->time_stamp - 1});
          // }
      }

      // Since this logic is identical to the historically operator, we use the
      // same conditionals before inverting the result

      intrvl = r2u2_boxq_peek(boxq);

      if (boxq->interval.start > monitor->time_stamp) {
        // Insufficient data, true by definition
        R2U2_DEBUG_PRINT("\t  Startup behavior: t < lower bound\n");
        *res = true;
      } else if (intrvl.start != r2u2_infinity) {
        R2U2_DEBUG_PRINT("\tChecking interval start\n");
        if (boxq->interval.end > monitor->time_stamp) {
            R2U2_DEBUG_PRINT("\t  Partial interval check: (%d == 0) = %c\n", intrvl.start, (intrvl.start == 0)?'T':'F');
            *res = intrvl.start == 0;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d <= %d) = %c\n", intrvl.start, boxq->interval.end, monitor->time_stamp, (intrvl.start + boxq->interval.end <= monitor->time_stamp)?'T':'F');
            *res = intrvl.start + boxq->interval.end <= monitor->time_stamp;
        }

        R2U2_DEBUG_PRINT("\tChecking interval end:\n");
        if (intrvl.end == r2u2_infinity) {
            R2U2_DEBUG_PRINT("\t  Open interval: T\n");
            *res &= true;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d >= %d) = %c\n", intrvl.end, boxq->interval.start, monitor->time_stamp, (intrvl.end + boxq->interval.start >= monitor->time_stamp)?'T':'F');
            *res &= intrvl.end + boxq->interval.start >= monitor->time_stamp;
        }
      } else {
        R2U2_DEBUG_PRINT("\tNo interval to check\n");
        *res = false;
      }

      *res = !*res;
      R2U2_DEBUG_PRINT("\tPT[%zu] = %d\n", instr->memory_reference, *res);

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_HISTORICALLY: {
      boxq = &(((r2u2_boxq_t*)(*(monitor->past_time_queue_mem)))[instr->memory_reference]);
      R2U2_DEBUG_PRINT("\tPT[%zu] H[%d,%d] PT[%d]\n", instr->memory_reference, boxq->interval.start, boxq->interval.end, instr->op1.value);
      intrvl = r2u2_boxq_peek(boxq);
      if ((intrvl.end != r2u2_infinity) && (intrvl.end + boxq->interval.start) < monitor->time_stamp) {
          intrvl = r2u2_boxq_pop_tail(boxq);
          R2U2_DEBUG_PRINT("\tGarbage collection, popping interval [%d, %d]\n", intrvl.start, intrvl.end);
      }

      edge = get_operand_edge(monitor, instr, 0);
      if (edge == R2U2_MLTL_PT_OPRND_EDGE_RISING) {
          // Start new open interval on rising edge
          R2U2_DEBUG_PRINT("\tRising edge detected, pushing to queue\n");
          r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){monitor->time_stamp, r2u2_infinity});
      }
      else if ((edge == R2U2_MLTL_PT_OPRND_EDGE_FALLING) && !r2u2_boxq_is_empty(boxq)) {
          // Here we can close the interval
          // However, as an optimization, we discard infeasible intervals
          R2U2_DEBUG_PRINT("\tFalling edge detected, closing interval\n");
          intrvl = r2u2_boxq_pop_head(boxq);
          r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){intrvl.start, monitor->time_stamp - 1});
          // TODO(bckempa): Verify and re-enable this optimization - don't store intervals that will never be true
          // if(((monitor->time_stamp + boxq->interval.start) >= (intrvl.start + boxq->interval.end + 1)) && ((monitor->time_stamp == 0) || (boxq->interval.start >= 1))){
          //     r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){intrvl.start, monitor->time_stamp - 1});
          //     R2U2_DEBUG_PRINT("\t\tAdding valid interval to queue: [%d, %d]\n", intrvl.start, monitor->time_stamp - 1);
          // }
      }

      intrvl = r2u2_boxq_peek(boxq);

      if (boxq->interval.start > monitor->time_stamp) {
        // Insufficient data, true by definition
        R2U2_DEBUG_PRINT("\t  Startup behavior: t < lower bound\n");
        *res = true;
      } else if (intrvl.start != r2u2_infinity) {
        R2U2_DEBUG_PRINT("\tChecking interval start\n");
        if (boxq->interval.end > monitor->time_stamp) {
            R2U2_DEBUG_PRINT("\t  Partial interval check: (%d == 0) = %c\n", intrvl.start, (intrvl.start == 0)?'T':'F');
            *res = intrvl.start == 0;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d <= %d) = %c\n", intrvl.start, boxq->interval.end, monitor->time_stamp, (intrvl.start + boxq->interval.end <= monitor->time_stamp)?'T':'F');
            *res = intrvl.start + boxq->interval.end <= monitor->time_stamp;
        }

        R2U2_DEBUG_PRINT("\tChecking interval end:\n");
        if (intrvl.end == r2u2_infinity) {
            R2U2_DEBUG_PRINT("\t  Open interval: T\n");
            *res &= true;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d >= %d) = %c\n", intrvl.end, boxq->interval.start, monitor->time_stamp, (intrvl.end + boxq->interval.start >= monitor->time_stamp)?'T':'F');
            *res &= intrvl.end + boxq->interval.start >= monitor->time_stamp;
        }
      } else {
        R2U2_DEBUG_PRINT("\tNo interval to check\n");
        *res = false;
      }

      R2U2_DEBUG_PRINT("\tPT[%zu] = %d\n", instr->memory_reference, *res);

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_SINCE: {
      // Works similar to Once, but with additional reset logic when

      boxq = &(((r2u2_boxq_t*)(*(monitor->past_time_queue_mem)))[instr->memory_reference]);
      R2U2_DEBUG_PRINT("\tPT[%zu] S[%d,%d] PT[%d] PT[%d]\n", instr->memory_reference, boxq->interval.start, boxq->interval.end, instr->op1.value, instr->op2.value);
      intrvl = r2u2_boxq_peek(boxq);
      if ((intrvl.end != r2u2_infinity) && (intrvl.end + boxq->interval.start) < monitor->time_stamp) {
          intrvl = r2u2_boxq_pop_tail(boxq);
          R2U2_DEBUG_PRINT("\tGarbage collection, popping interval [%d, %d]\n", intrvl.start, intrvl.end);
      }

      if (get_operand(monitor, instr, 0)) {
          R2U2_DEBUG_PRINT("\tLeft operand holds, testing right operand edge\n");
          edge = get_operand_edge(monitor, instr, 1);
          if (edge == R2U2_MLTL_PT_OPRND_EDGE_FALLING) {
              R2U2_DEBUG_PRINT("\tFalling edge detected on right operand, pushing to queue\n");
              r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){monitor->time_stamp, r2u2_infinity});
          } else if ((edge == R2U2_MLTL_PT_OPRND_EDGE_RISING) && !r2u2_boxq_is_empty(boxq)) {
              R2U2_DEBUG_PRINT("\tRising edge detected on right operand, closing interval\n");
              intrvl = r2u2_boxq_pop_head(boxq);
              r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){intrvl.start, monitor->time_stamp - 1});
              // TODO(bckempa): Verify and re-enable this optimization - don't store intervals that will never be true
              // if(((monitor->time_stamp + boxq->interval.start) >= (intrvl.start + boxq->interval.end + 1)) && ((monitor->time_stamp == 0) || (boxq->interval.start >= 1))){
              //     r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){intrvl.start, monitor->time_stamp - 1});
              // }
          }
      } else { // p1 does not hold
          R2U2_DEBUG_PRINT("\tLeft operand false, resetting based on right operand\n");
          if (get_operand(monitor, instr, 1)) {
              R2U2_DEBUG_PRINT("\tRight operand holds, setting queue\n");
              r2u2_boxq_reset(boxq);
              if (monitor->time_stamp != 0) {
                r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){0, monitor->time_stamp - 1});
              }
          } else {
              R2U2_DEBUG_PRINT("\tRight operand false, resetting queue\n");
              intrvl = r2u2_boxq_pop_tail(boxq);
              r2u2_boxq_push(boxq, (r2u2_boxq_intvl_t){0, r2u2_infinity});
          }
      }
      intrvl = r2u2_boxq_peek(boxq);

      if (boxq->interval.start > monitor->time_stamp) {
        // Insufficient data, true by definition
        R2U2_DEBUG_PRINT("\t  Startup behavior: t < lower bound\n");
        *res = true;
      } else if (intrvl.start != r2u2_infinity) {
        R2U2_DEBUG_PRINT("\tChecking interval start\n");
        if (boxq->interval.end > monitor->time_stamp) {
            R2U2_DEBUG_PRINT("\t  Partial interval check: (%d == 0) = %c\n", intrvl.start, (intrvl.start == 0)?'T':'F');
            *res = intrvl.start == 0;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d <= %d) = %c\n", intrvl.start, boxq->interval.end, monitor->time_stamp, (intrvl.start + boxq->interval.end <= monitor->time_stamp)?'T':'F');
            *res = intrvl.start + boxq->interval.end <= monitor->time_stamp;
        }

        R2U2_DEBUG_PRINT("\tChecking interval end:\n");
        if (intrvl.end == r2u2_infinity) {
            R2U2_DEBUG_PRINT("\t  Open interval: T\n");
            *res &= true;
        } else {
            R2U2_DEBUG_PRINT("\t  Standard interval check: (%d + %d >= %d) = %c\n", intrvl.end, boxq->interval.start, monitor->time_stamp, (intrvl.end + boxq->interval.start >= monitor->time_stamp)?'T':'F');
            *res &= intrvl.end + boxq->interval.start >= monitor->time_stamp;
        }
      } else {
        R2U2_DEBUG_PRINT("\tNo interval to check\n");
        *res = false;
      }

      *res = !*res;
      R2U2_DEBUG_PRINT("\tPT[%zu] = %d\n", instr->memory_reference, *res);

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_LOCK: {
      R2U2_DEBUG_PRINT("\tPT[%zu] LOCK\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }

    case R2U2_MLTL_OP_PT_NOT: {
      R2U2_DEBUG_PRINT("\tPT[%zu] NOT PT[%d]\t", instr->memory_reference, instr->op1.value);
      *res = !get_operand(monitor, instr, 0);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_AND: {
      R2U2_DEBUG_PRINT("\tPT[%zu] AND PT[%d] PT[%d]\t", instr->memory_reference, instr->op1.value, instr->op2.value);
      *res = get_operand(monitor, instr, 0) && get_operand(monitor, instr, 1);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_OR: {
      R2U2_DEBUG_PRINT("\tPT[%zu] OR PT[%d]\t", instr->memory_reference, instr->op1.value);
      *res = get_operand(monitor, instr, 0) || get_operand(monitor, instr, 1);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_PT_IMPLIES: {
      R2U2_DEBUG_PRINT("\tPT[%zu] IMPLIES PT[%d] PT[%d]\t", instr->memory_reference, instr->op1.value, instr->op2.value);
      *res = (!get_operand(monitor, instr, 0)) || get_operand(monitor, instr, 1);
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }

    case R2U2_MLTL_OP_PT_NAND: {
      R2U2_DEBUG_PRINT("\tPT[%zu] NAND\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_NOR: {
      R2U2_DEBUG_PRINT("\tPT[%zu] NOR\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_XOR: {
      R2U2_DEBUG_PRINT("\tPT[%zu] XOR\n", instr->memory_reference);
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_PT_EQUIVALENT: {
      R2U2_DEBUG_PRINT("\tPT[%zu] EQUIVALENT PT[%d] PT[%d]\t", instr->memory_reference, instr->op2.value);
      *res = (get_operand(monitor, instr, 0) == get_operand(monitor, instr, 1));
      R2U2_DEBUG_PRINT("= %d\n", *res);
      error_cond = R2U2_OK;
      break;
    }
    default: {
      // Somehow got into wrong tense dispatch
      error_cond = R2U2_INVALID_INST;
      break;
    }
  }

  return error_cond;
}
