#include "r2u2.h"
#include "future_time.h"
#include "prediction.h"
#include "../engines/atomic_checker/atomic_checker.h"
#include "../engines/booleanizer/booleanizer.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))

static r2u2_bool operand_data_ready(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {

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

        res = !r2u2_scq_is_empty(target_scq, rd_ptr, &(source_scq->desired_time_stamp), monitor->predictive_mode);
        break;

      case R2U2_FT_OP_NOT_SET:
          // TODO(bckempa): This should set R2U2 error?
          res = false;
          break;
    }

    return res;
}

static r2u2_verdict get_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n) {

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
          source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
          res.time = source_scq->desired_time_stamp;
          if (source_scq->prob == 2.0){ //Indicates probabilistic operator
            res.prob = op->value;
          }else{
            res.truth = op->value;
          }
          break;

      case R2U2_FT_OP_ATOMIC:
          // TODO(bckempa) This might remove the need for load...
          source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
          res.time = source_scq->desired_time_stamp;
          if (source_scq->prob == 2.0){ // Indicates probabilistic operator
            if ((*(monitor->atomic_prob_buffer))[op->value] < 0)
              res.prob = (*(monitor->atomic_buffer[0]))[op->value] ? 1.0 : 0.0;
            else
              res.prob = (*(monitor->atomic_buffer[0]))[op->value] ? (*(monitor->atomic_prob_buffer))[op->value] : 1-(*(monitor->atomic_prob_buffer))[op->value];
          }else{
            res.truth = (*(monitor->atomic_buffer[0]))[op->value];
          }
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

static r2u2_verdict get_child_operand(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, int n, r2u2_time *rd_ptr) {

    r2u2_verdict res;
    r2u2_mltl_operand_t *op;
    r2u2_scq_t *source_scq, *target_scq;

    if (n == 0) {
      op = &(instr->op1);
    } else {
      op = &(instr->op2);
    }

    switch (op->opnd_type) {
      case R2U2_FT_OP_DIRECT:
          source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
          res.time = source_scq->desired_time_stamp;
          if (source_scq->prob == 2.0){ //Indicates probabilistic operator
            res.prob = op->value;
          }else{
            res.truth = op->value;
          }
          break;

      case R2U2_FT_OP_ATOMIC:
          source_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);
          res.time = source_scq->desired_time_stamp;
          if (source_scq->prob == 2.0){ // Indicates probabilistic operator
            if ((*(monitor->atomic_prob_buffer))[op->value] < 0)
              res.prob = (*(monitor->atomic_buffer[0]))[op->value] ? 1.0 : 0.0;
            else
              res.prob = (*(monitor->atomic_buffer[0]))[op->value] ? (*(monitor->atomic_prob_buffer))[op->value] : 1-(*(monitor->atomic_prob_buffer))[op->value];
          }else{
            res.truth = (*(monitor->atomic_buffer[0]))[op->value];
          }
          break;

      case R2U2_FT_OP_SUBFORMULA:
        target_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[op->value]);
        res = r2u2_scq_pop(target_scq, rd_ptr);
        break;
    }

    return res;
}

static r2u2_status_t push_result(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_verdict *res) {
  // Pushes result to SCQ, sets tau and flags progress if nedded
  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->memory_reference]);

  if(monitor->predictive_mode){
    r2u2_scq_push(scq, res, &scq->pred_wr_ptr);
  }else{
    r2u2_scq_push(scq, res, &scq->wr_ptr);
  }

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
      scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->op1.value]);

      switch (instr->op2.opnd_type) {
        case R2U2_FT_OP_DIRECT: {
          // TODO(bckempa): Lots of queue logic here, move to `shared_connection_queue.c`
          scq->length = instr->op2.value;
          r2u2_verdict *elements = ((r2u2_verdict*)(*(monitor->future_time_queue_mem)));
          // TODO(bckempa): need better sizing of array extents when switch elements
          // TODO(bckempa): ANSAN requires offset due to global layout shadow, fix and remove "+ 50"
          scq->queue = &(elements[(R2U2_MAX_SCQ_BYTES / sizeof(r2u2_verdict)) - (instr->memory_reference + 50)]);
          scq->queue[0].time = r2u2_infinity;  // Initialize empty queue
          R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tSCQ Len: %d\n\t\tSCQ Offset: %u\n\t\tAddr: %p\n", instr->op1.value, scq->length, instr->memory_reference, (void*)scq->queue);
          scq->deadline = INT32_MAX;
          scq->k_modes = 1;
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
          if(instr->op2.value == 0){
            R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tLB: %u\n", instr->op1.value, instr->memory_reference);
            scq->interval_start = (r2u2_time) instr->memory_reference;
          } else if (instr->op2.value == 1) {
            R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tUB: %u\n", instr->op1.value, instr->memory_reference);
            scq->interval_end = (r2u2_time) instr->memory_reference;
          } else if(instr->op2.value == 2){
            R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tDeadline: %d\n", instr->op1.value, instr->memory_reference);
            scq->deadline = (r2u2_int) instr->memory_reference;
          } else if(instr->op2.value == 3){
            R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tK: %d\n", instr->op1.value, instr->memory_reference);
            scq->k_modes = (r2u2_time) instr->memory_reference;
          } else if(instr->op2.value == 4){
            R2U2_DEBUG_PRINT("\t\tInst: %d\n\t\tProbability: %d\n", instr->op1.value, instr->memory_reference);
            scq->prob = instr->memory_reference / 1000000.0;
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
          fprintf(monitor->out_file, "%d:%u,%s\n", instr->op2.value, res.time, res.truth ? "T" : "F");
        }

        if (monitor->out_func != NULL) {
          (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &res);
        }

        if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        
      }

      // Multimodal Model Predictive Runtime Verification
      if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS){
        if((int)monitor->time_stamp - (int)scq->deadline >= 0){ // T_R - d >= 0
          r2u2_time index = monitor->time_stamp - scq->deadline;
          operand_data_ready(monitor, instr, 0);
          res = get_operand(monitor, instr, 0);
          if(res.time == r2u2_infinity || res.time < index && scq->desired_time_stamp <= index){ // last i produced < index; therefore, prediction required
            monitor->predictive_mode = true;
            r2u2_mltl_instruction_t* mltl_instructions[R2U2_MAX_INSTRUCTIONS];
            r2u2_bz_instruction_t* bz_instructions[R2U2_MAX_BZ_INSTRUCTIONS];
            r2u2_scq_state_t prev_real_state[R2U2_MAX_INSTRUCTIONS];
            r2u2_time k_trace_offset[scq->k_modes];
            r2u2_time k_prob_offset[scq->k_modes];
            size_t num_mltl_instructions, num_bz_instructions = 0;
            // Find child instructions for ft and booleanizer assembly (atomic checker not currently supported)
            r2u2_status_t status = find_child_instructions(monitor, &(*monitor->instruction_tbl)[monitor->prog_count], mltl_instructions, &num_mltl_instructions, 
                                                            bz_instructions, &num_bz_instructions, monitor->prog_count - instr->memory_reference);
            find_k_start_index(monitor, k_trace_offset, k_prob_offset, scq->k_modes);
            prep_prediction_scq(monitor, mltl_instructions, instr, prev_real_state, num_mltl_instructions);
            r2u2_signal_vector_t *signal_vector_original = monitor->signal_vector;
            r2u2_atomic_buffer_t *atomic_prob_buffer_original = monitor->atomic_prob_buffer;

            r2u2_time iteration = 0;
            while(res.time == r2u2_infinity || res.time < index){ // while prediction is required
              monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP; // reset monitor state
              
              r2u2_float temp_prob_buffer[monitor->num_atomics];
              for(int j = 0; j < (int)scq->k_modes; j++){
                monitor->signal_vector = &(*(signal_vector_original))[k_trace_offset[j]+(iteration*monitor->num_signals)];
                monitor->atomic_prob_buffer = &(*(atomic_prob_buffer_original))[k_prob_offset[j]+(iteration*monitor->num_atomics)];
                if(k_prob_offset[j] == 0 && scq->k_modes > 1){
                  for(int k = 0; k < monitor->num_atomics; k++){
                    (*(monitor->atomic_prob_buffer))[k] = 1.0 / scq->k_modes;
                  }
                }
                for(int i = num_bz_instructions - 1; i >= 0; i--){ // dispatch booleanizer instructions
                  R2U2_DEBUG_PRINT("%d.%d.%zu.%d\n",monitor->time_stamp,iteration, i, j);
                  if(bz_instructions[i]->store && j != 0) {
                    r2u2_float prev_prob = temp_prob_buffer[bz_instructions[i]->at_addr];
                    r2u2_bool prev_atomic = (*(monitor->atomic_buffer)[0])[bz_instructions[i]->at_addr];
                    r2u2_bz_instruction_dispatch(monitor, bz_instructions[i]);
                    if(prev_atomic && !((*(monitor->atomic_buffer)[0])[bz_instructions[i]->at_addr])){ // Going from true to false
                      temp_prob_buffer[bz_instructions[i]->at_addr] = (*(monitor->atomic_prob_buffer))[bz_instructions[i]->at_addr];
                      (*(monitor->atomic_buffer)[0])[bz_instructions[i]->at_addr] = false;
                    }else if(prev_atomic == ((*(monitor->atomic_buffer)[0])[bz_instructions[i]->at_addr])){ // Staying same atomic value
                      temp_prob_buffer[bz_instructions[i]->at_addr] = prev_prob + (*(monitor->atomic_prob_buffer))[bz_instructions[i]->at_addr];
                    }else{ // Value is false and will remain false even if true for one mode
                      (*(monitor->atomic_buffer)[0])[bz_instructions[i]->at_addr] = prev_atomic;
                    }
                  }else{
                    r2u2_bz_instruction_dispatch(monitor, bz_instructions[i]);
                    temp_prob_buffer[bz_instructions[i]->at_addr] = (*(monitor->atomic_prob_buffer))[bz_instructions[i]->at_addr];
                  }
                }
              }
              monitor->atomic_prob_buffer = &temp_prob_buffer;
              iteration++;

              while(true){ // continue until no progress is made
                for(int i = num_mltl_instructions - 1; i >= 0; i--){ // dispatch ft instructions
                  R2U2_DEBUG_PRINT("%d.%d.%zu.%d\n",monitor->time_stamp, iteration-1, i, monitor->progress);
                  r2u2_mltl_ft_update(monitor, mltl_instructions[i]);
                }
                R2U2_DEBUG_PRINT("\tFT RETURN\n");
                if(operand_data_ready(monitor, instr, 0)){
                  res = get_operand(monitor, instr, 0);
                  // Only store result up to 'index'; don't predict for values after 'index'
                  scq->desired_time_stamp = min(index, res.time) + 1;
                  r2u2_verdict result = {min(index, res.time), res.truth};
                  r2u2_scq_push(scq, &result, &scq->pred_wr_ptr);

                  if (monitor->out_file != NULL) {
                    fprintf(monitor->out_file, "%d:%u,%s (Predicted at time stamp %d)\n", instr->op2.value, min(index, res.time), res.truth ? "T" : "F", monitor->time_stamp);
                  }

                  if (monitor->out_func != NULL) {
                    (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &res);
                  }

                  if(min(index, res.time) == index){
                    monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS;
                    break;
                  }
                }
                if(monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS){
                  break;
                }
                monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS;
              }
            }
            restore_scq(monitor, mltl_instructions, instr, prev_real_state, num_mltl_instructions);
            monitor->signal_vector = signal_vector_original;
            monitor->atomic_prob_buffer = atomic_prob_buffer_original;
            monitor->predictive_mode = false;
          }
        }
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

          // We only need to see every timestep once, even if we don't output
          scq->desired_time_stamp = (op0.time)+1;

        if(scq->prob == 2.0){ //Indicates probabilisitic operator
          if (op0.time >= scq->interval_end){
            r2u2_float p_temp = op0.prob;
            R2U2_DEBUG_PRINT("\t\tp_temp = %lf\n", p_temp);
            r2u2_scq_t *target_scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->op1.value]);
            for(int t = 1; t <= (scq->interval_end-scq->interval_start); t++){ //Iterate backwards through operand queue
              r2u2_time curr_index = ((int)scq->rd_ptr - t < 0) ? (target_scq->length) + ((int)scq->rd_ptr - t) : (scq->rd_ptr - t);
              p_temp = p_temp * get_child_operand(monitor, instr, 0, &curr_index).prob;
              R2U2_DEBUG_PRINT("\t\tp_temp = p_temp * %lf = %lf\n", get_child_operand(monitor, instr, 0, &curr_index).prob, p_temp);
            }
            res.time = op0.time - scq->interval_end;
            res.prob = p_temp;
            r2u2_scq_push(scq, &res, monitor->predictive_mode ? &scq->pred_wr_ptr : &scq->wr_ptr);
          }
        }else{
          // interval compression aware rising edge detection
          if(op0.truth && !scq->previous.truth) {
            scq->edge = scq->previous.time + 1;
            R2U2_DEBUG_PRINT("\tRising edge at t= %d\n", scq->edge);
          }

          if (op0.truth && (op0.time >= scq->interval_end - scq->interval_start + scq->edge) && (op0.time >= scq->interval_end)) {
            res = (r2u2_verdict){op0.time - scq->interval_end, true};
            r2u2_scq_push(scq, &res, monitor->predictive_mode ? &scq->pred_wr_ptr : &scq->wr_ptr);
            R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
            if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          } else if (!op0.truth && (op0.time >= scq->interval_start)) {
            res = (r2u2_verdict){op0.time - scq->interval_start, false};
            r2u2_scq_push(scq, &res, monitor->predictive_mode ? &scq->pred_wr_ptr : &scq->wr_ptr);
            R2U2_DEBUG_PRINT("\t(%d, %d)\n", res.time, res.truth);
            if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
          }

          scq->previous = op0;
        }
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

        if(scq->prob == 2.0){ //Indicates probabilisitic operator
          if (op0.time >= scq->interval_end){
            r2u2_float p_temp = op1.prob;
            R2U2_DEBUG_PRINT("p_temp = %lf\n", p_temp);
            r2u2_scq_t *target_scq1 = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->op1.value]);
            r2u2_scq_t *target_scq2 = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instr->op2.value]);
            for(int t = 1; t <= (scq->interval_end-scq->interval_start); t++){ //Iterate backwards through operand queue
              r2u2_time curr_index1 = ((int)scq->rd_ptr - t < 0) ? (target_scq1->length) + ((int)scq->rd_ptr - t) : (scq->rd_ptr - t);
              r2u2_time curr_index2 = ((int)scq->rd_ptr2 - t < 0) ? (target_scq2->length) + ((int)scq->rd_ptr2 - t) : (scq->rd_ptr2 - t);
              p_temp = p_temp * get_child_operand(monitor, instr, 0, &curr_index1).prob;
              R2U2_DEBUG_PRINT("p_temp = p_temp * %lf = %lf\n", get_child_operand(monitor, instr, 0, &curr_index1).prob, p_temp);
              p_temp = 1 - ((1 - get_child_operand(monitor, instr, 1, &curr_index2).prob)*(1 - p_temp));
              R2U2_DEBUG_PRINT("p_temp = 1 - ((1 - %lf) * (1 - p_temp)) = %lf\n", get_child_operand(monitor, instr, 1, &curr_index2).prob, p_temp);
            }
            res.time = op0.time - scq->interval_end;
            res.prob = p_temp;
            r2u2_scq_push(scq, &res, monitor->predictive_mode ? &scq->pred_wr_ptr : &scq->wr_ptr);
          }
        }else{
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
            r2u2_scq_push(scq, &res, monitor->predictive_mode ? &scq->pred_wr_ptr : &scq->wr_ptr);
            R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
            if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
            scq->max_out = res.time +1;
          } else if (!op0.truth && (tau >= scq->max_out + scq->interval_start)) {
            R2U2_DEBUG_PRINT("\tLeft Op False\n");
            res = (r2u2_verdict){tau - scq->interval_start, false};
            r2u2_scq_push(scq, &res, monitor->predictive_mode ? &scq->pred_wr_ptr : &scq->wr_ptr);
            R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
            if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
            scq->max_out = res.time +1;
          } else if ((tau >= scq->interval_end - scq->interval_start + scq->edge) && (tau >= scq->max_out + scq->interval_end)) {
            R2U2_DEBUG_PRINT("\tTime Elapsed\n");
            res = (r2u2_verdict){tau - scq->interval_end, false};
            r2u2_scq_push(scq, &res, monitor->predictive_mode ? &scq->pred_wr_ptr : &scq->wr_ptr);
            R2U2_DEBUG_PRINT("\t(%d,%d)\n", res.time, res.truth);
            if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
            scq->max_out = res.time +1;
          }

          scq->previous = op1;
        }
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
        if (scq->prob == 2.0){ // Indicates probabilistic operator
          res.prob = 1 - res.prob;
        }else{
          res.truth = !res.truth;
        }
        push_result(monitor, instr, &res);
      }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_AND: {
      R2U2_DEBUG_PRINT("\tFT AND\n");

      op0_rdy = operand_data_ready(monitor, instr, 0);
      op1_rdy = operand_data_ready(monitor, instr, 1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (scq->prob == 2.0){ // Indicates probabilistic operator
        if (op0_rdy && op1_rdy) {
          op0 = get_operand(monitor, instr, 0);
          op1 = get_operand(monitor, instr, 1);
          res.time = op0.time;
          res.prob = op0.prob * op1.prob;
          push_result(monitor, instr, &res);
        }
      }
      else{
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

    case R2U2_MLTL_OP_FT_PROB: {
      R2U2_DEBUG_PRINT("\tFT PROB\n");

      if (operand_data_ready(monitor, instr, 0)) {
        res = get_operand(monitor, instr, 0);
        R2U2_DEBUG_PRINT("\t\tProbability for i = %d is %f\n", res.time, res.prob);
        push_result(monitor, instr, &(r2u2_verdict){res.time, res.prob >= scq->prob});
      }

      error_cond = R2U2_OK;
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
      error_cond = R2U2_INVALID_INST;
      break;
    }
  }

  return error_cond;
}
