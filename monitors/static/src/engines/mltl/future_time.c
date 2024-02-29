#include "r2u2.h"

#include "future_time.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))

static r2u2_bool operand_data_ready(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {

    r2u2_bool res;
    r2u2_time *rd_ptr;
    r2u2_scq_t *source_scq, *target_scq;

    r2u2_mltl_operand_type_t type;
    uint32_t value;

    type  = (n == 0) ? (instr->op1_type)  : (instr->op2_type);
    value = (n == 0) ? (instr->op1_value) : (instr->op2_value);

    switch (type) {

      case R2U2_FT_OP_DIRECT:
        res = true;
        break;

      case R2U2_FT_OP_ATOMIC:
        // Only load in atomics on first loop of time step
        res = (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP);
        break;

      case R2U2_FT_OP_SUBFORMULA:
        source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
        target_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[value]);

        rd_ptr  = (n == 0) ? &(source_scq->rd_ptr) : &(source_scq->rd_ptr2);

        res = !r2u2_scq_is_empty(target_scq, rd_ptr, &(source_scq->desired_time_stamp));
        break;

      case R2U2_FT_OP_NOT_SET:
          // TODO(bckempa): This should set R2U2 error?
          res = false;
          break;

      default:
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          res = false;
          break;
    }

    return res;
}

static r2u2_verdict get_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {

    r2u2_verdict res;
    r2u2_time *rd_ptr;
    r2u2_scq_t *source_scq, *target_scq;

    r2u2_mltl_operand_type_t type;
    uint32_t value;

    type  = (n == 0) ? (instr->op1_type)  : (instr->op2_type);
    value = (n == 0) ? (instr->op1_value) : (instr->op2_value);


    switch (type) {

      case R2U2_FT_OP_DIRECT:
          res = (r2u2_verdict){monitor->time_stamp, value};
          break;

      case R2U2_FT_OP_ATOMIC:
          // TODO(bckempa) This might remove the need for load...
          res = (r2u2_verdict){monitor->time_stamp, (*(monitor->atomic_buffer[0]))[value]};
          break;

      case R2U2_FT_OP_SUBFORMULA:
        source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
        target_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[value]);

        rd_ptr  = (n == 0) ? &(source_scq->rd_ptr) : &(source_scq->rd_ptr2);

        // NOTE: Must always check if queue is empty before poping
        // in tis case we always call operand_data_ready first
        res = r2u2_scq_pop(target_scq, rd_ptr);
        break;

      case R2U2_FT_OP_NOT_SET:
          // TODO(bckempa): This should set R2U2 error?
          res = (r2u2_verdict){0};
          break;

      default:
          R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
          res = (r2u2_verdict){0};
          break;
    }

    return res;
}

static r2u2_status_t push_result(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_verdict *res) {
  // Pushes result to SCQ, sets tau and flags progress if nedded
  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);

  r2u2_scq_push(scq, res);
  R2U2_DEBUG_PRINT("\t(%d,%d)\n", res->time, res->truth);

  scq->desired_time_stamp = (res->time)+1;

  // TODO(bckempa): Inline or macro this
  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

  return R2U2_OK;
}

r2u2_status_t r2u2_mltl_ft_update(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr) {

  r2u2_verdict op0, op1, res;
  r2u2_status_t error_cond;
  r2u2_bool op0_rdy, op1_rdy;

  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);

  switch (instr->opcode) {
    case R2U2_MLTL_OP_FT_NOP: {
      R2U2_DEBUG_PRINT("\tFT NOP\n");
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_CONFIGURE: {
      R2U2_DEBUG_PRINT("\tFT Configure\n");

      // Configuration store target SCQ index in first operand instead
      scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->op1_value]);

      switch (instr->op2_type) {
        case R2U2_FT_OP_DIRECT: {
          // TODO(bckempa): Lots of queue logic here, move to `shared_connection_queue.c`
          scq->length = instr->op2_value;
          r2u2_verdict *elements = ((r2u2_verdict*)(*(monitor->future_time_queue_mem)));
          // TODO(bckempa): need better sizing of array extents when switch elements
          // TODO(bckempa): ANSAN requires offset due to global layout shadow, fix and remove "+ 50"
          scq->queue = &(elements[(R2U2_MAX_SCQ_BYTES / sizeof(r2u2_verdict)) - (instr->memory_reference + 50)]);
          scq->queue[0].time = r2u2_infinity;  // Initialize empty queue
          R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tSCQ Len: %d\n\t\tSCQ Offset: %u\n\t\tAddr: %p\n", instr->op1_value, scq->length, instr->memory_reference, (void*)scq->queue);

          #if R2U2_DEBUG
          // Check for SCQ memory arena collision
          assert(scq+1 < (r2u2_scq_t*)&(elements[(R2U2_MAX_SCQ_BYTES / sizeof(r2u2_verdict)) - (instr->memory_reference + scq->length + 50)]));
          #endif

          // Rise/Fall edge detection initialization
          switch (instr->opcode) {
            case R2U2_MLTL_OP_FT_GLOBALLY:
                scq->previous = (r2u2_verdict) {r2u2_infinity, false};
                break;
            case R2U2_MLTL_OP_FT_UNTIL:
                scq->previous = (r2u2_verdict) {r2u2_infinity, true};
                break;
            default:
                scq->previous = (r2u2_verdict) {0, true};
          }

          break;
        }
        case R2U2_FT_OP_ATOMIC: {
          // Encodes interval in mem_ref; op[1] is low (0) or high (1) bound
          if (instr->op2_value) {
            R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tUB: %u\n", instr->op1_value, instr->memory_reference);
            scq->interval_end = (r2u2_time) instr->memory_reference;
          } else {
            R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tLB: %u\n", instr->op1_value, instr->memory_reference);
            scq->interval_start = (r2u2_time) instr->memory_reference;
          }
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
    case R2U2_MLTL_OP_FT_LOAD: {
      R2U2_DEBUG_PRINT("\tFT LOAD\n");

      if (operand_data_ready(monitor, instr, 0)) {
        res = get_operand(monitor, instr, 0);
        push_result(monitor, instr, &res);
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_RETURN: {
      R2U2_DEBUG_PRINT("\tFT RETURN\n");

      if (operand_data_ready(monitor, instr, 0)) {
        res = get_operand(monitor, instr, 0);
        R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
        scq->desired_time_stamp = (res.time)+1;

        if (monitor->out_file != NULL) {
          fprintf(monitor->out_file, "%d:%u,%s\n", instr->op2_value, res.time, res.truth ? "T" : "F");
        }

        if (monitor->out_func != NULL) {
          (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &res);
        }

        if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
      }

      error_cond = R2U2_OK;
      break;
    }

    case R2U2_MLTL_OP_FT_EVENTUALLY: {
      R2U2_DEBUG_PRINT("\tFT EVENTUALLY\n");
      error_cond = R2U2_UNIMPL;
      break;
    }
    case R2U2_MLTL_OP_FT_GLOBALLY: {
      R2U2_DEBUG_PRINT("\tFT GLOBALLY\n");

      if (operand_data_ready(monitor, instr, 0)) {
        op0 = get_operand(monitor, instr, 0);

        // We only need to see every timesetp once, even if we don't output
        scq->desired_time_stamp = (op0.time)+1;

        // interval compression aware rising edge detection
        if(op0.truth && !scq->previous.truth) {
          scq->edge = scq->previous.time + 1;
          R2U2_DEBUG_PRINT("\tRising edge at t= %d\n", scq->edge);
        }

        if (op0.truth && (op0.time >= scq->interval_end - scq->interval_start + scq->edge) && (op0.time >= scq->interval_end)) {
          res = (r2u2_verdict){op0.time - scq->interval_end, true};
          r2u2_scq_push(scq, &res);
          R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        } else if (!op0.truth && (op0.time >= scq->interval_start)) {
          res = (r2u2_verdict){op0.time - scq->interval_start, false};
          r2u2_scq_push(scq, &res);
          R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        }

        scq->previous = op0;
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_UNTIL: {
      R2U2_DEBUG_PRINT("\tFT UNTIL\n");

      if (operand_data_ready(monitor, instr, 0) && operand_data_ready(monitor, instr, 1)) {
        op0 = get_operand(monitor, instr, 0);
        op1 = get_operand(monitor, instr, 1);

        // We need to see every timesetp as an op0 op1 pair
        r2u2_time tau = min(op0.time, op1.time);
        scq->desired_time_stamp = tau+1;

        // interval compression aware falling edge detection on op1
        if(!op1.truth && scq->previous.truth) {
          // TODO(bckempa): Not clear why this isn't stil pre.time+1
          scq->edge = scq->previous.time;
          R2U2_DEBUG_PRINT("\tRight operand falling edge at t=%d\n", scq->edge);
        }

        if (op1.truth && (tau >= scq->max_out + scq->interval_start)) {
          // TODO(bckempa): Factor out repeated outuput logic
          R2U2_DEBUG_PRINT("\tRight Op True\n");
          res = (r2u2_verdict){tau - scq->interval_start, true};
          r2u2_scq_push(scq, &res);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time +1;
        } else if (!op0.truth && (tau >= scq->max_out + scq->interval_start)) {
          R2U2_DEBUG_PRINT("\tLeft Op False\n");
          res = (r2u2_verdict){tau - scq->interval_start, false};
          r2u2_scq_push(scq, &res);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time +1;
        } else if ((tau >= scq->interval_end - scq->interval_start + scq->edge) && (tau >= scq->max_out + scq->interval_end)) {
          R2U2_DEBUG_PRINT("\tTime Elapsed\n");
          res = (r2u2_verdict){tau - scq->interval_end, false};
          r2u2_scq_push(scq, &res);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time +1;
        }

        scq->previous = op1;

      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_RELEASE: {
      R2U2_DEBUG_PRINT("\tFT RELEASE\n");
      error_cond = R2U2_UNIMPL;
      break;
    }

    case R2U2_MLTL_OP_FT_NOT: {
      R2U2_DEBUG_PRINT("\tFT NOT\n");

      if (operand_data_ready(monitor, instr, 0)) {
        res = get_operand(monitor, instr, 0);
        push_result(monitor, instr, &(r2u2_verdict){res.time, !res.truth});
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_AND: {
      R2U2_DEBUG_PRINT("\tFT AND\n");

      op0_rdy = operand_data_ready(monitor, instr, 0);
      op1_rdy = operand_data_ready(monitor, instr, 1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (op0_rdy && op1_rdy) {
        op0 = get_operand(monitor, instr, 0);
        op1 = get_operand(monitor, instr, 1);
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", op0.time, op0.truth, op1.time, op1.truth);
        if (op0.truth && op1.truth){
          R2U2_DEBUG_PRINT("\tBoth True\n");
          push_result(monitor, instr, &(r2u2_verdict){min(op0.time, op1.time), true});
        } else if (!op0.truth && !op1.truth) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          push_result(monitor, instr, &(r2u2_verdict){max(op0.time, op1.time), false});
        } else if (op0.truth) {
          R2U2_DEBUG_PRINT("\tOnly Left True\n");
          push_result(monitor, instr, &(r2u2_verdict){op1.time, false});
        } else {
          R2U2_DEBUG_PRINT("\tOnly Right True\n");
          push_result(monitor, instr, &(r2u2_verdict){op0.time, false});
        }
      } else if (op0_rdy) {
        op0 = get_operand(monitor, instr, 0);
        R2U2_DEBUG_PRINT("\tOnly Left Ready: (%d, %d)\n", op0.time, op0.truth);
        if(!op0.truth) {
          push_result(monitor, instr, &(r2u2_verdict){op0.time, false});
        }
      } else if (op1_rdy) {
        op1 = get_operand(monitor, instr, 1);
        R2U2_DEBUG_PRINT("\tOnly Right Ready: (%d, %d)\n", op1.time, op1.truth);
        if(!op1.truth) {
          push_result(monitor, instr, &(r2u2_verdict){op1.time, false});
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
    default: {
      // Somehow got into wrong tense dispatch
      R2U2_DEBUG_PRINT("Warning: Bad Inst Type\n");
      error_cond = R2U2_INVALID_INST;
      break;
    }
  }

  return error_cond;
}
