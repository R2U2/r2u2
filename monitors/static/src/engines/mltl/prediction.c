#include "r2u2.h"
#include "prediction.h"
#include <stdlib.h>

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))

r2u2_bool predicted_operand_data_ready(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {

    r2u2_bool res;
    r2u2_time *rd_ptr;
    r2u2_mltl_operand_t *op;
    r2u2_scq_t *source_scq, *target_scq;

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
        res = true;
        break;

      case R2U2_FT_OP_ATOMIC:
        // Only load in atomics on first loop of time step
        res = (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP);
        break;

      case R2U2_FT_OP_SUBFORMULA:
        source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
        target_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[op->value]);

        if (n==0) {
          rd_ptr = &(source_scq->rd_ptr);
        } else {
          rd_ptr = &(source_scq->rd_ptr2);
        }

        res = !r2u2_scq_is_empty(target_scq, rd_ptr, &(source_scq->desired_time_stamp), true);
        break;

      case R2U2_FT_OP_NOT_SET:
          // TODO(bckempa): This should set R2U2 error?
          res = false;
          break;
    }

    return res;
}

r2u2_verdict get_predicted_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {

    r2u2_verdict res;
    r2u2_time *rd_ptr;
    r2u2_mltl_operand_t *op;
    r2u2_scq_t *source_scq, *target_scq;

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
          res = (r2u2_verdict){r2u2_infinity, op->value};
          break;
      
      case R2U2_FT_OP_ATOMIC:
          // TODO(bckempa) This might remove the need for load...
          source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
          res = (r2u2_verdict){source_scq->desired_time_stamp, (*(monitor->atomic_buffer[0]))[op->value]};
          break;

      case R2U2_FT_OP_SUBFORMULA:
        source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
        target_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[op->value]);

        if (n==0) {
          rd_ptr = &(source_scq->rd_ptr);
        } else {
          rd_ptr = &(source_scq->rd_ptr2);
        }

        // NOTE: Must always check if queue is empty before poping
        // in tis case we always call operand_data_ready first
        res = r2u2_scq_pop(target_scq, rd_ptr);
        break;

      case R2U2_FT_OP_NOT_SET:
          // TODO(bckempa): This should set R2U2 error?
          res = (r2u2_verdict){0};
          break;
    }

    return res;
}

static r2u2_status_t push_result_predicted(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_verdict *res) {
  // Pushes result to SCQ, sets tau and flags progress if nedded
  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);

  r2u2_scq_push(scq, res, &scq->pred_wr_ptr);
  R2U2_DEBUG_PRINT("\t(%d,%d)\n", res->time, res->truth);

  scq->desired_time_stamp = (res->time)+1;

  // TODO(bckempa): Inline or macro this
  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

  return R2U2_OK;
}

// Helper function to find booleanizer child instruction for MLTL atomic
r2u2_status_t find_bz_child_instructions(r2u2_monitor_t *monitor, r2u2_instruction_t *instr, r2u2_instruction_t** instructions, size_t *size, uint8_t desired_atom, uint8_t curr_index){
  if(instr->engine_tag == R2U2_ENG_BZ){
    r2u2_bz_instruction_t* bz_instr = ((r2u2_bz_instruction_t*)instr->instruction_data);
    if (bz_instr->store == 1 && bz_instr->at_addr == desired_atom){
      instructions = realloc(instructions, sizeof(instructions) + sizeof(r2u2_instruction_t*));
      instructions[*size] = &(*monitor->instruction_tbl)[curr_index];
      *size = *size + 1;
      return find_child_instructions(monitor, instructions[*size-1], instructions, size, 0);
    }
    else if(curr_index == 0){
      return R2U2_INVALID_INST;
    }
    else{
      instr = &(*monitor->instruction_tbl)[curr_index-1];
      return find_bz_child_instructions(monitor, instr, instructions, size, desired_atom, curr_index-1);
    }
  }
  return R2U2_INVALID_INST;
}


r2u2_status_t find_child_instructions(r2u2_monitor_t *monitor, r2u2_instruction_t *instr, r2u2_instruction_t** instructions, size_t *size, uint8_t difference){
  if(instr->engine_tag == R2U2_ENG_TL) {
    r2u2_mltl_instruction_t* mltl_instr = (r2u2_mltl_instruction_t*)instr->instruction_data;
    switch (mltl_instr->opcode){
      case R2U2_MLTL_OP_FT_LOAD: {
        instr = &(*monitor->instruction_tbl)[difference-1];
        return find_bz_child_instructions(monitor, instr, instructions, size, mltl_instr->op1.value, difference-1);
      }
      case R2U2_MLTL_OP_FT_RETURN: {
        instructions[0] = &(*monitor->instruction_tbl)[mltl_instr->op1.value+difference];
        *size = 1;
        return find_child_instructions(monitor, instructions[0], instructions, size, difference);
      }
      case R2U2_MLTL_OP_FT_GLOBALLY:
      case R2U2_MLTL_OP_FT_NOT: {
        if(mltl_instr->op1.opnd_type == R2U2_FT_OP_ATOMIC || mltl_instr->op1.opnd_type == R2U2_FT_OP_SUBFORMULA){
          instructions = realloc(instructions, sizeof(instructions) + sizeof(r2u2_instruction_t*));
          instructions[*size] = &(*monitor->instruction_tbl)[mltl_instr->op1.value+difference];
          *size = *size + 1;
          return find_child_instructions(monitor, instructions[*size-1], instructions, size, difference);
        }else{
          return R2U2_OK;
        }
      }
      case R2U2_MLTL_OP_FT_UNTIL:
      case R2U2_MLTL_OP_FT_AND: {
        r2u2_status_t status = R2U2_OK;
        if(mltl_instr->op1.opnd_type == R2U2_FT_OP_ATOMIC || mltl_instr->op1.opnd_type == R2U2_FT_OP_SUBFORMULA){
          instructions = realloc(instructions, sizeof(instructions) + sizeof(r2u2_mltl_instruction_t*));
          instructions[*size] = &(*monitor->instruction_tbl)[mltl_instr->op1.value+difference];
          *size = *size + 1;
          status = find_child_instructions(monitor, instructions[*size-1], instructions, size, difference);
        }
        if(status == R2U2_OK && (mltl_instr->op2.opnd_type == R2U2_FT_OP_ATOMIC || mltl_instr->op2.opnd_type == R2U2_FT_OP_SUBFORMULA)){
          instructions = realloc(instructions, sizeof(instructions) + sizeof(r2u2_mltl_instruction_t*));
          instructions[*size] = &(*monitor->instruction_tbl)[mltl_instr->op2.value+difference];
          *size = *size + 1;
          return find_child_instructions(monitor, instructions[*size-1], instructions, size, difference);
        }else{
          return status;
        }
      }
      case R2U2_MLTL_OP_FT_EVENTUALLY:
      case R2U2_MLTL_OP_FT_RELEASE:
      case R2U2_MLTL_OP_FT_OR:
      case R2U2_MLTL_OP_FT_IMPLIES:
      case R2U2_MLTL_OP_FT_NAND:
      case R2U2_MLTL_OP_FT_NOR:
      case R2U2_MLTL_OP_FT_XOR:
      case R2U2_MLTL_OP_FT_EQUIVALENT: {
        return R2U2_UNIMPL;
      }
      case R2U2_MLTL_OP_FT_NOP: {
        return R2U2_OK;
      }
      default: {
        // Somehow got into wrong tense dispatch
        return R2U2_INVALID_INST;
      }
    }
  }else if(instr->engine_tag == R2U2_ENG_BZ){
    r2u2_bz_instruction_t* bz_instr = ((r2u2_bz_instruction_t*)instr->instruction_data);
    switch (bz_instr->opcode){
      case R2U2_BZ_OP_NONE:
      case R2U2_BZ_OP_ILOAD:
      case R2U2_BZ_OP_FLOAD:
      case R2U2_BZ_OP_ICONST:
      case R2U2_BZ_OP_FCONST: {
        return R2U2_OK;
      }
      case R2U2_BZ_OP_BWNEG:
      case R2U2_BZ_OP_INEG:
      case R2U2_BZ_OP_FNEG:
      case R2U2_BZ_OP_ISQRT:
      case R2U2_BZ_OP_FSQRT: {
        instructions = realloc(instructions, sizeof(instructions) + sizeof(r2u2_instruction_t*));
        instructions[*size] = &(*monitor->instruction_tbl)[bz_instr->param1.bz_addr];
        *size = *size + 1;
        return find_child_instructions(monitor, instructions[*size-1], instructions, size, difference);
      } 
      case R2U2_BZ_OP_BWAND:
      case R2U2_BZ_OP_BWOR:
      case R2U2_BZ_OP_BWXOR:
      case R2U2_BZ_OP_IEQ:
      case R2U2_BZ_OP_FEQ:
      case R2U2_BZ_OP_INEQ:
      case R2U2_BZ_OP_FNEQ:
      case R2U2_BZ_OP_IGT:
      case R2U2_BZ_OP_FGT:
      case R2U2_BZ_OP_IGTE:
      case R2U2_BZ_OP_ILT:
      case R2U2_BZ_OP_FLT:
      case R2U2_BZ_OP_ILTE:
      case R2U2_BZ_OP_IADD:
      case R2U2_BZ_OP_FADD:
      case R2U2_BZ_OP_ISUB:
      case R2U2_BZ_OP_FSUB:
      case R2U2_BZ_OP_IMUL:
      case R2U2_BZ_OP_FMUL:
      case R2U2_BZ_OP_IDIV:
      case R2U2_BZ_OP_FDIV:
      case R2U2_BZ_OP_MOD:
      case R2U2_BZ_OP_IPOW:
      case R2U2_BZ_OP_FPOW:{
        instructions = realloc(instructions, sizeof(instructions) + sizeof(r2u2_instruction_t*));
        instructions[*size] = &(*monitor->instruction_tbl)[bz_instr->param1.bz_addr];
        *size = *size + 1;
        r2u2_status_t status = find_child_instructions(monitor, instructions[*size-1], instructions, size, difference);
        if(status == R2U2_OK){
          instructions = realloc(instructions, sizeof(instructions) + sizeof(r2u2_instruction_t*));
          instructions[*size] = &(*monitor->instruction_tbl)[bz_instr->param2.bz_addr];
          *size = *size + 1;
          return find_child_instructions(monitor, instructions[*size-1], instructions, size, difference);
        }
      }
      default: {
        return R2U2_INVALID_INST;
      }
    }
  }
  return R2U2_OK;
}

r2u2_status_t r2u2_mltl_ft_predict(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr) {
  r2u2_verdict op0, op1, res;
  r2u2_status_t error_cond;
  r2u2_bool op0_rdy, op1_rdy;

  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);

  switch (instr->opcode) {
    case R2U2_MLTL_OP_FT_NOP: {
      R2U2_DEBUG_PRINT("\tFT PREDICT NOP\n");
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_LOAD: {
      R2U2_DEBUG_PRINT("\tFT PREDICT LOAD\n");
      if (predicted_operand_data_ready(monitor, instr, 0)) {
        res = get_predicted_operand(monitor, instr, 0);
        push_result_predicted(monitor, instr, &res);
      }
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_GLOBALLY: {
      R2U2_DEBUG_PRINT("\tFT PREDICT GLOBALLY\n");

      if (predicted_operand_data_ready(monitor, instr, 0)) {
        op0 = get_predicted_operand(monitor, instr, 0);

        // We only need to see every timesetp once, even if we don't output
        scq->desired_time_stamp = (op0.time)+1;

        // interval compression aware rising edge detection
        if(op0.truth && !scq->previous.truth) {
          scq->edge = scq->previous.time + 1;
          R2U2_DEBUG_PRINT("\tRising edge at t= %d\n", scq->edge);
        }

        if (op0.truth && (op0.time >= scq->interval_end - scq->interval_start + scq->edge) && (op0.time >= scq->interval_end)) {
          res = (r2u2_verdict){op0.time - scq->interval_end, true};
          r2u2_scq_push(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        } else if (!op0.truth && (op0.time >= scq->interval_start)) {
          res = (r2u2_verdict){op0.time - scq->interval_start, false};
          r2u2_scq_push(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        }

        scq->previous = op0;
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_UNTIL: {
      R2U2_DEBUG_PRINT("\tFT PREDICT UNTIL\n");

      if (predicted_operand_data_ready(monitor, instr, 0) && predicted_operand_data_ready(monitor, instr, 1)) {
        op0 = get_predicted_operand(monitor, instr, 0);
        op1 = get_predicted_operand(monitor, instr, 1);

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
          // TODO(bckempa): Factor out repeated output logic
          R2U2_DEBUG_PRINT("\tRight Op True\n");
          res = (r2u2_verdict){tau - scq->interval_start, true};
          r2u2_scq_push(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time + 1;
        } else if (!op0.truth && (tau >= scq->max_out + scq->interval_start)) {
          R2U2_DEBUG_PRINT("\tLeft Op False\n");
          res = (r2u2_verdict){tau - scq->interval_start, false};
          r2u2_scq_push(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time +1;
        } else if ((tau >= scq->interval_end - scq->interval_start + scq->edge) && (tau >= scq->max_out + scq->interval_end)) {
          R2U2_DEBUG_PRINT("\tTime Elapsed\n");
          res = (r2u2_verdict){tau - scq->interval_end, false};
          r2u2_scq_push(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time + 1;
        }

        scq->previous = op1;

      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_RELEASE: {
      R2U2_DEBUG_PRINT("\tFT PREDICT RELEASE\n");
      error_cond = R2U2_UNIMPL;
      break;
    }

    case R2U2_MLTL_OP_FT_NOT: {
      R2U2_DEBUG_PRINT("\tFT PREDICT NOT\n");

      if (predicted_operand_data_ready(monitor, instr, 0)) {
        res = get_predicted_operand(monitor, instr, 0);
        push_result_predicted(monitor, instr, &(r2u2_verdict){res.time, !res.truth});
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_AND: {
      R2U2_DEBUG_PRINT("\tFT PREDICT AND\n");

      op0_rdy = predicted_operand_data_ready(monitor, instr, 0);
      op1_rdy = predicted_operand_data_ready(monitor, instr, 1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (op0_rdy && op1_rdy) {
        op0 = get_predicted_operand(monitor, instr, 0);
        op1 = get_predicted_operand(monitor, instr, 1);
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %d) (%d, %d)\n", op0.time, op0.truth, op1.time, op1.truth);
        if (op0.truth && op1.truth){
          R2U2_DEBUG_PRINT("\tBoth True\n");
          push_result_predicted(monitor, instr, &(r2u2_verdict){min(op0.time, op1.time), true});
        } else if (!op0.truth && !op1.truth) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          push_result_predicted(monitor, instr, &(r2u2_verdict){max(op0.time, op1.time), false});
        } else if (op0.truth) {
          R2U2_DEBUG_PRINT("\tOnly Left True\n");
          push_result_predicted(monitor, instr, &(r2u2_verdict){op1.time, false});
        } else {
          R2U2_DEBUG_PRINT("\tOnly Right True\n");
          push_result_predicted(monitor, instr, &(r2u2_verdict){op0.time, false});
        }
      } else if (op0_rdy) {
        op0 = get_predicted_operand(monitor, instr, 0);
        R2U2_DEBUG_PRINT("\tOnly Left Ready: (%d, %d)\n", op0.time, op0.truth);
        if(!op0.truth) {
          push_result_predicted(monitor, instr, &(r2u2_verdict){op0.time, false});
        }
      } else if (op1_rdy) {
        op1 = get_predicted_operand(monitor, instr, 1);
        R2U2_DEBUG_PRINT("\tOnly Right Ready: (%d, %d)\n", op1.time, op1.truth);
        if(!op1.truth) {
          push_result_predicted(monitor, instr, &(r2u2_verdict){op1.time, false});
        }
      }
      
      error_cond = R2U2_OK;
      break;
    }
    default: {
      // Somehow processed a instruction that was not valid
      error_cond = R2U2_INVALID_INST;
      break;
    }
  }

  return error_cond;
}

void prep_prediction_scq(r2u2_monitor_t *monitor, r2u2_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size){
  R2U2_DEBUG_PRINT("-----------------Starting New Round of Prediction (at time stamp %d)-----------------\n", monitor->time_stamp);
  for(size_t i = 0; i < size; i++){
    if(instructions[i]->engine_tag == R2U2_ENG_TL){
      r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[((r2u2_mltl_instruction_t*)instructions[i]->instruction_data)->memory_reference]);
      prev_real_state[i].rd_ptr = scq->rd_ptr;
      prev_real_state[i].rd_ptr2 = scq->rd_ptr2;
      prev_real_state[i].desired_time_stamp = scq->desired_time_stamp;
      prev_real_state[i].edge = scq->edge;
      prev_real_state[i].max_out = scq->max_out;
      prev_real_state[i].previous = scq->previous;
      scq->pred_wr_ptr = scq->wr_ptr;
    }
  }
}

void restore_scq(r2u2_monitor_t *monitor, r2u2_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size){
  for(size_t i = 0; i < size; i++){
    if(instructions[i]->engine_tag == R2U2_ENG_TL){
      r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[((r2u2_mltl_instruction_t*)instructions[i]->instruction_data)->memory_reference]);
      scq->rd_ptr = prev_real_state[i].rd_ptr;
      scq->rd_ptr2 = prev_real_state[i].rd_ptr2;
      scq->desired_time_stamp = prev_real_state[i].desired_time_stamp;
      scq->edge = prev_real_state[i].edge;
      scq->max_out = prev_real_state[i].max_out;
      scq->previous = prev_real_state[i].previous;
    }
  }
}

