#include "r2u2.h"
#include "prediction.h"
#include <stdlib.h>
#include <math.h>

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
          res = (r2u2_verdict){r2u2_infinity, op->value, 1.0};
          break;
      
      case R2U2_FT_OP_ATOMIC:
          // TODO(bckempa) This might remove the need for load...
          source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
          res = (r2u2_verdict){source_scq->desired_time_stamp, (*(monitor->atomic_buffer[0]))[op->value],(*(monitor->atomic_prob_buffer))[op->value]};
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

static r2u2_status_t r2u2_scq_push_predicted(r2u2_scq_t *scq, r2u2_verdict *res, r2u2_time *wr_ptr) {
  R2U2_DEBUG_PRINT("\t\tPushing to SCQ <%p> Length: (%d)\n", (void*)scq->queue, scq->length);
  R2U2_DEBUG_PRINT("\t\tWrite Pointer Pre: [%d]<%p> -> (%d, %d, %f)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth, (scq->queue)[-((ptrdiff_t)*wr_ptr)].prob);
  #if R2U2_DEBUG
  r2u2_scq_print(scq, NULL);
  #endif

  // When overwriting predicted data with real data reset pred_wr_ptr
  if(wr_ptr == &scq->wr_ptr && *wr_ptr == scq->pred_wr_ptr){
    scq->pred_wr_ptr = r2u2_infinity;
  }

  // TODO(bckempa): Verify compiler removes redundant modulo arith, else inline
  if ((scq->queue)[-((ptrdiff_t)*wr_ptr)].time == r2u2_infinity) {
    // Initialization behavior
    R2U2_DEBUG_PRINT("\t\tInitial Write\n");
    (scq->queue)[-((ptrdiff_t)*wr_ptr)] = *res;
    *wr_ptr = (*wr_ptr + 1) % scq->length;
    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d, %f)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth,  (scq->queue)[-((ptrdiff_t)*wr_ptr)].prob);
    #if R2U2_DEBUG
    r2u2_scq_print(scq, NULL);
    #endif
    return R2U2_OK;
  }
  #ifndef R2U2_PROBABILISTIC
  if (((scq->queue)[-((ptrdiff_t)((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1))].truth == res->truth) && \
      ((scq->queue)[-((ptrdiff_t)((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1))].time < res->time) && \
      (scq->wr_ptr != scq->pred_wr_ptr)) {
    R2U2_DEBUG_PRINT("\t\tAggregate Write\n");
    // Aggregate write, overwrite the previous cell to update timestamp
    (scq->queue)[-((ptrdiff_t)((*wr_ptr == 0) ? scq->length-1 : *wr_ptr-1))] = *res;

    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth);
    #if R2U2_DEBUG
    r2u2_scq_print(scq, NULL);
    #endif
    return R2U2_OK;
  } else 
  #endif
  {
    // Standard write
    R2U2_DEBUG_PRINT("\t\tStandard Write\n");
    (scq->queue)[-((ptrdiff_t)*wr_ptr)] = *res;
    if(wr_ptr == &scq->pred_wr_ptr){ // Ensure that predicted data never overwrites real relevant data
      *wr_ptr = (((*wr_ptr + 1) % scq->length) == ((scq->wr_ptr + ((scq->length-1)/2)+1) % scq->length)) ? *wr_ptr = scq->wr_ptr : ((*wr_ptr + 1) % scq->length);
    }else{
      *wr_ptr = (*wr_ptr + 1) % scq->length;
    }
    R2U2_DEBUG_PRINT("\t\tWrite Pointer Post: [%d]<%p> -> (%d, %d, %f)\n", *wr_ptr, (void*)&((scq->queue)[-((ptrdiff_t)*wr_ptr)]), (scq->queue)[-((ptrdiff_t)*wr_ptr)].time, (scq->queue)[-((ptrdiff_t)*wr_ptr)].truth, (scq->queue)[-((ptrdiff_t)*wr_ptr)].prob);
    #if R2U2_DEBUG
    r2u2_scq_print(scq, NULL);
    #endif
    return R2U2_OK;
  }
  return R2U2_ERR_OTHER;
}

static r2u2_status_t push_result_predicted(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_verdict *res) {
  // Pushes result to SCQ, sets tau and flags progress if nedded
  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);

  r2u2_scq_push_predicted(scq, res, &scq->pred_wr_ptr);
  R2U2_DEBUG_PRINT("\t(%d,%d)\n", res->time, res->truth);

  scq->desired_time_stamp = (res->time)+1;

  // TODO(bckempa): Inline or macro this
  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

  return R2U2_OK;
}

r2u2_status_t r2u2_mltl_ft_predict(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_verdict* scq_prob_buffer) {
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

        // We only need to see every timestep once, even if we don't output
        scq->desired_time_stamp = (op0.time)+1;

        #ifdef R2U2_PROBABILISTIC
        for(int i = 0; i < (scq->interval_end-scq->interval_start); i++){
          R2U2_DEBUG_PRINT("Previous value at %d: (%d, %s, %f)\n", i, scq_prob_buffer[i].time, scq_prob_buffer[i].truth ? "T" : "F", scq_prob_buffer[i].prob);
        }
          for(int i = 0; i < (scq->interval_end-scq->interval_start); i++){
            if(scq_prob_buffer[i].time == op0.time-scq->interval_end && (int)scq_prob_buffer[i].time >= 0){
              R2U2_DEBUG_PRINT("Pushing %d with previous value: (%d, %s, %f)\n", op0.time, scq_prob_buffer[i].time, scq_prob_buffer[i].truth ? "T" : "F", scq_prob_buffer[i].prob);
              res = (r2u2_verdict){op0.time - scq->interval_end, scq_prob_buffer[i].truth && op0.truth, scq_prob_buffer[i].prob * op0.prob};
              r2u2_scq_push_predicted(scq, &res, &scq->pred_wr_ptr);
              R2U2_DEBUG_PRINT("Initializing %d to overwrite %d with: (%d, %s, %f)\n", op0.time, op0.time-scq->interval_end, op0.time, op0.truth ? "T" : "F", op0.prob);
              scq_prob_buffer[i] = (r2u2_verdict){op0.time, op0.truth, op0.prob}; 
            }
            else if((int)scq_prob_buffer[i].time > (int)(op0.time-scq->interval_end) && (int)scq_prob_buffer[i].time >= 0){
              R2U2_DEBUG_PRINT("Adding %d to previous values: (%d, %s, %f)\n", op0.time, scq_prob_buffer[i].time, scq_prob_buffer[i].truth ? "T" : "F", scq_prob_buffer[i].prob);
              scq_prob_buffer[i].truth = scq_prob_buffer[i].truth && op0.truth;
              scq_prob_buffer[i].prob = scq_prob_buffer[i].prob * op0.prob;
            }
            else{
              R2U2_DEBUG_PRINT("Initializing %d with: (%d, %s, %f)\n", op0.time, op0.time, op0.truth ? "T" : "F", op0.prob);
              scq_prob_buffer[i] = op0;
              break;
            }
          }
        #else

        // interval compression aware rising edge detection
        if(op0.truth && !scq->previous.truth) {
          scq->edge = scq->previous.time + 1;
          R2U2_DEBUG_PRINT("\tRising edge at t= %d\n", scq->edge);
        }

        if (op0.truth && (op0.time >= scq->interval_end - scq->interval_start + scq->edge) && (op0.time >= scq->interval_end)) {
          res = (r2u2_verdict){op0.time - scq->interval_end, true, 1.0}; //To-Do
          r2u2_scq_push_predicted(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        } 
        else if (!op0.truth && (op0.time >= scq->interval_start)) {
          res = (r2u2_verdict){op0.time - scq->interval_start, false, 0.0}; //To-Do
          r2u2_scq_push_predicted(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        }
        #endif

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
          res = (r2u2_verdict){tau - scq->interval_start, true, 1.0}; //To-Do
          r2u2_scq_push_predicted(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time + 1;
        } else if (!op0.truth && (tau >= scq->max_out + scq->interval_start)) {
          R2U2_DEBUG_PRINT("\tLeft Op False\n");
          res = (r2u2_verdict){tau - scq->interval_start, false, 0.0}; //To-Do
          r2u2_scq_push_predicted(scq, &res, &scq->pred_wr_ptr);
          R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
          if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          scq->max_out = res.time +1;
        } else if ((tau >= scq->interval_end - scq->interval_start + scq->edge) && (tau >= scq->max_out + scq->interval_end)) {
          R2U2_DEBUG_PRINT("\tTime Elapsed\n");
          res = (r2u2_verdict){tau - scq->interval_end, false, 0.0}; //To-Do
          r2u2_scq_push_predicted(scq, &res, &scq->pred_wr_ptr);
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
        push_result_predicted(monitor, instr, &(r2u2_verdict){res.time, !res.truth, 1-res.prob});
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
          push_result_predicted(monitor, instr, &(r2u2_verdict){min(op0.time, op1.time), true, op0.prob * op1.prob});
        } else if (!op0.truth && !op1.truth) {
          R2U2_DEBUG_PRINT("\tBoth False\n");
          push_result_predicted(monitor, instr, &(r2u2_verdict){max(op0.time, op1.time), false, op0.prob * op1.prob});
        } else if (op0.truth) {
          R2U2_DEBUG_PRINT("\tOnly Left True\n");
          push_result_predicted(monitor, instr, &(r2u2_verdict){op1.time, false, op0.prob * op1.prob});
        } else {
          R2U2_DEBUG_PRINT("\tOnly Right True\n");
          push_result_predicted(monitor, instr, &(r2u2_verdict){op0.time, false, op0.prob * op1.prob});
        }
      } 
      #ifndef R2U2_PROBABILISTIC
      else if (op0_rdy) {
        op0 = get_predicted_operand(monitor, instr, 0);
        R2U2_DEBUG_PRINT("\tOnly Left Ready: (%d, %d)\n", op0.time, op0.truth);
        if(!op0.truth) {
          push_result_predicted(monitor, instr, &(r2u2_verdict){op0.time, false, 0.0}); //To-Do
        }
      } else if (op1_rdy) {
        op1 = get_predicted_operand(monitor, instr, 1);
        R2U2_DEBUG_PRINT("\tOnly Right Ready: (%d, %d)\n", op1.time, op1.truth);
        if(!op1.truth) {
          push_result_predicted(monitor, instr, &(r2u2_verdict){op1.time, false, 0.0}); //To-Do
        }
      }
      #endif
      
      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_PROB: {
      R2U2_DEBUG_PRINT("\tFT PREDICT PROB\n");

      if (predicted_operand_data_ready(monitor, instr, 0)) {
        res = get_predicted_operand(monitor, instr, 0);
        push_result_predicted(monitor, instr, &(r2u2_verdict){res.time, res.prob >= scq->prob, 1.0});
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

r2u2_status_t r2u2_bz_predict(r2u2_monitor_t *monitor, r2u2_bz_instruction_t *instr, r2u2_time k_mode, float prob)
{
    r2u2_status_t status = R2U2_OK;
    if(instr->store) {
        if(k_mode == 0){
          status = r2u2_bz_instruction_dispatch(monitor, instr);
          #ifdef R2U2_PROBABILISTIC
          (*(monitor->atomic_prob_buffer))[instr->at_addr] = ((*(monitor->atomic_buffer)[0])[instr->at_addr] ? prob : 0.0);
          #endif
        }
        else{
          r2u2_bool prev_atomic = (*(monitor->atomic_buffer)[0])[instr->at_addr];
          status = r2u2_bz_instruction_dispatch(monitor, instr);
          #ifdef R2U2_PROBABILISTIC
          r2u2_float prev_prob = (*(monitor->atomic_prob_buffer))[instr->at_addr];
          (*(monitor->atomic_prob_buffer))[instr->at_addr] = prev_prob + ((*(monitor->atomic_buffer)[0])[instr->at_addr] ? prob : 0.0);
          #endif
          (*(monitor->atomic_buffer)[0])[instr->at_addr] = prev_atomic && (*(monitor->atomic_buffer)[0])[instr->at_addr];
        }
    }
    else{
      status = r2u2_bz_instruction_dispatch(monitor, instr);
    }

    return status;
}

// Helper function to find booleanizer child instruction for MLTL atomic
r2u2_status_t find_bz_child_instructions(r2u2_monitor_t *monitor, r2u2_instruction_t *instr, r2u2_mltl_instruction_t** mltl_instructions, size_t *mltl_size, r2u2_bz_instruction_t** bz_instructions, size_t *bz_size, uint8_t desired_atom, uint8_t curr_index){
  if(instr->engine_tag == R2U2_ENG_BZ){
    r2u2_bz_instruction_t* bz_instr = ((r2u2_bz_instruction_t*)instr->instruction_data);
    if (bz_instr->store == 1 && bz_instr->at_addr == desired_atom){
      instr = &(*monitor->instruction_tbl)[curr_index];
      bz_instructions[*bz_size] = (r2u2_bz_instruction_t*)(instr->instruction_data);
      *bz_size = *bz_size + 1;
      return find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, 0);
    }
    else if(curr_index == 0){
      return R2U2_INVALID_INST;
    }
    else{
      instr = &(*monitor->instruction_tbl)[curr_index-1];
      return find_bz_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, desired_atom, curr_index-1);
    }
  }
  return R2U2_INVALID_INST;
}


r2u2_status_t find_child_instructions(r2u2_monitor_t *monitor, r2u2_instruction_t *instr, r2u2_mltl_instruction_t** mltl_instructions, size_t *mltl_size, r2u2_bz_instruction_t** bz_instructions, size_t *bz_size, uint8_t difference){
  if(instr->engine_tag == R2U2_ENG_TL) {
    r2u2_mltl_instruction_t* mltl_instr = (r2u2_mltl_instruction_t*)instr->instruction_data;
    switch (mltl_instr->opcode){
      case R2U2_MLTL_OP_FT_LOAD: {
        instr = &(*monitor->instruction_tbl)[difference-1];
        return find_bz_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, mltl_instr->op1.value, difference-1);
      }
      case R2U2_MLTL_OP_FT_RETURN: {
        instr = &(*monitor->instruction_tbl)[mltl_instr->op1.value+difference];
        mltl_instructions[0] = (r2u2_mltl_instruction_t*)(instr->instruction_data);
        *mltl_size = 1;
        return find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, difference);
      }
      case R2U2_MLTL_OP_FT_GLOBALLY:
      case R2U2_MLTL_OP_FT_NOT: 
      case R2U2_MLTL_OP_FT_PROB:{
        if(mltl_instr->op1.opnd_type == R2U2_FT_OP_ATOMIC || mltl_instr->op1.opnd_type == R2U2_FT_OP_SUBFORMULA){
          instr = &(*monitor->instruction_tbl)[mltl_instr->op1.value+difference];
          mltl_instructions[*mltl_size] = (r2u2_mltl_instruction_t*)(instr->instruction_data);
          *mltl_size = *mltl_size + 1;
          return find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, difference);
        }else{
          return R2U2_OK;
        }
      }
      case R2U2_MLTL_OP_FT_UNTIL:
      case R2U2_MLTL_OP_FT_AND: {
        r2u2_status_t status = R2U2_OK;
        if(mltl_instr->op1.opnd_type == R2U2_FT_OP_ATOMIC || mltl_instr->op1.opnd_type == R2U2_FT_OP_SUBFORMULA){
          instr = &(*monitor->instruction_tbl)[mltl_instr->op1.value+difference];
          mltl_instructions[*mltl_size] = (r2u2_mltl_instruction_t*)(instr->instruction_data);
          *mltl_size = *mltl_size + 1;
          status = find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, difference);
        }
        if(status == R2U2_OK && (mltl_instr->op2.opnd_type == R2U2_FT_OP_ATOMIC || mltl_instr->op2.opnd_type == R2U2_FT_OP_SUBFORMULA)){
          instr = &(*monitor->instruction_tbl)[mltl_instr->op2.value+difference];
          mltl_instructions[*mltl_size] = (r2u2_mltl_instruction_t*)(instr->instruction_data);
          *mltl_size = *mltl_size + 1;
          return find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, difference);
        }else{
          return status;
        }
      }
      case R2U2_MLTL_OP_FT_EVENTUALLY:
      case R2U2_MLTL_OP_FT_RELEASE:
      case R2U2_MLTL_OP_FT_OR:
      case R2U2_MLTL_OP_FT_IMPLIES:
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
        instr = &(*monitor->instruction_tbl)[bz_instr->param1.bz_addr];
        bz_instructions[*bz_size] = (r2u2_bz_instruction_t*)(instr->instruction_data);
        *bz_size = *bz_size + 1;
        return find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, difference);
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
        instr = &(*monitor->instruction_tbl)[bz_instr->param1.bz_addr];
        bz_instructions[*bz_size] = (r2u2_bz_instruction_t*)(instr->instruction_data);
        *bz_size = *bz_size + 1;
        r2u2_status_t status = find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, difference);
        if(status == R2U2_OK){
          instr = &(*monitor->instruction_tbl)[bz_instr->param2.bz_addr];
          bz_instructions[*bz_size] = (r2u2_bz_instruction_t*)(instr->instruction_data);
          *bz_size = *bz_size + 1;
          return find_child_instructions(monitor, instr, mltl_instructions, mltl_size, bz_instructions, bz_size, difference);
        }
      }
      default: {
        return R2U2_INVALID_INST;
      }
    }
  }
  return R2U2_OK;
}

void find_trace_start_index(r2u2_monitor_t *monitor, r2u2_time* trace_start_index, size_t size){
  int temp = 0;
  for(int i = 0; i < size; i++){
    while(true){
      if(strcmp((*(monitor->signal_vector))[temp], "|") == 0){
        trace_start_index[i] = temp+1;
        R2U2_DEBUG_PRINT("%d trace starts at %d\n", i, temp+1);
        temp = temp + monitor->num_signals + 1;
        break;
      }
      else{
        temp = temp + monitor->num_signals;
      }
    }
  }
}

void prep_prediction_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size){
  R2U2_DEBUG_PRINT("-----------------Starting New Round of Prediction (at time stamp %d)-----------------\n", monitor->time_stamp);
  for(size_t i = 0; i < size; i++){
      r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instructions[i]->memory_reference]);
      prev_real_state[i].rd_ptr = scq->rd_ptr;
      prev_real_state[i].rd_ptr2 = scq->rd_ptr2;
      prev_real_state[i].desired_time_stamp = scq->desired_time_stamp;
      prev_real_state[i].edge = scq->edge;
      prev_real_state[i].max_out = scq->max_out;
      prev_real_state[i].previous = scq->previous;
      scq->pred_wr_ptr = scq->wr_ptr;
  }
}

void restore_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_scq_state_t* prev_real_state, size_t size){
  for(size_t i = 0; i < size; i++){
      r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instructions[i]->memory_reference]);
      scq->rd_ptr = prev_real_state[i].rd_ptr;
      scq->rd_ptr2 = prev_real_state[i].rd_ptr2;
      scq->desired_time_stamp = prev_real_state[i].desired_time_stamp;
      scq->edge = prev_real_state[i].edge;
      scq->max_out = prev_real_state[i].max_out;
      scq->previous = prev_real_state[i].previous;
  }
}

void prep_prediction_prob(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_verdict** scq_prob_buffer, size_t size){
  for(size_t i = 0; i < size; i++){
    if(instructions[i]->opcode == R2U2_MLTL_OP_FT_GLOBALLY || instructions[i]->opcode == R2U2_MLTL_OP_FT_UNTIL){
      r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instructions[i]->memory_reference]);
      scq_prob_buffer[i] = malloc(sizeof(r2u2_verdict) * (scq->interval_end - scq->interval_start));
      for(int j = 0; j < (scq->interval_end - scq->interval_start); j++){
          scq_prob_buffer[i][j] = (r2u2_verdict){r2u2_infinity, false, 0.0};
      }
      if(scq->previous.truth){
        int temp = 0;
        for(int j = max((int)scq->edge, (int)(monitor->time_stamp - scq->interval_end)); j <= monitor->time_stamp; j++){
          scq_prob_buffer[i][temp] = (r2u2_verdict){j, true, 1.0};
          temp++;
        }
      }
    }
  }
}

