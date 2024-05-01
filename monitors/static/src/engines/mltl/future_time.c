#include "r2u2.h"
#include "future_time.h"
#include "prediction.h"
#include "../engines/atomic_checker/atomic_checker.h"
#include "../engines/booleanizer/booleanizer.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))

#if R2U2_PRED_PROB
static r2u2_bool check_operand_data_probability(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_bool op_num, r2u2_probability *result) {
    r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
    r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);
    r2u2_tnt_t *rd_ptr; // Hold off on this in case it doesn't exist...

    // Get operand info based on `n` which indicates left/first v.s. right/second
    r2u2_mltl_operand_type_t op_type = (op_num == 0) ? (instr->op1_type) : (instr->op2_type);
    uint32_t value = (op_num == 0) ? (instr->op1_value) : (instr->op2_value);

    switch (op_type) {

      case R2U2_FT_OP_DIRECT:
      // Only load in directs on first loop of time step
        result->time = monitor->time_stamp;
        result->prob = value;
        return (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP);

      case R2U2_FT_OP_ATOMIC:
        // Only load in atomics on first loop of time step
        result->time = monitor->time_stamp;
        if ((*(monitor->atomic_prob_buffer))[value] < 0)
            result->prob = (*(monitor->atomic_buffer[0]))[value] ? 1.0 : 0.0;
        else
          result->prob = (*(monitor->atomic_buffer[0]))[value] ? (*(monitor->atomic_prob_buffer))[value] : 1-(*(monitor->atomic_prob_buffer))[value];
        return (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP);

      case R2U2_FT_OP_SUBFORMULA:
        // Handled by the duo queue check function, just need the arguments
        rd_ptr = (op_num == 0) ? &(ctrl->read1) : &(ctrl->read2);

        return r2u2_duoq_ft_check_probability(arena, value, rd_ptr, ctrl->next_time, result, monitor->predictive_mode);

      case R2U2_FT_OP_NOT_SET:
        *result = (r2u2_probability){0};
        return false;

      default:
        R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
        *result = (r2u2_probability){0};
        return false;
    }
}
#endif
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
        return (monitor->progress == R2U2_MONITOR_PROGRESS_FIRST_LOOP);

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

        return r2u2_duoq_ft_check(arena, value, rd_ptr, ctrl->next_time, result, monitor->predictive_mode);

      case R2U2_FT_OP_NOT_SET:
        *result = 0;
        return false;

      default:
        R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
        *result = 0;
        return false;
    }
}

static r2u2_probability get_child_operand_probability(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_bool op_num, r2u2_time rd_ptr) {
    r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
    r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);

    // Get operand info based on `n` which indicates left/first v.s. right/second
    r2u2_mltl_operand_type_t op_type = (op_num == 0) ? (instr->op1_type) : (instr->op2_type);
    uint32_t value = (op_num == 0) ? (instr->op1_value) : (instr->op2_value);

    r2u2_probability result;

    switch (op_type) {
      
      case R2U2_FT_OP_DIRECT:
      // Only load in directs on first loop of time step
        result.time = monitor->time_stamp;
        result.prob = value;
        break;
      case R2U2_FT_OP_ATOMIC:
        // Only load in atomics on first loop of time step
        result.time = monitor->time_stamp;
        if ((*(monitor->atomic_prob_buffer))[value] < 0)
            result.prob = (*(monitor->atomic_buffer[0]))[value] ? 1.0 : 0.0;
        else
          result.prob = (*(monitor->atomic_buffer[0]))[value] ? (*(monitor->atomic_prob_buffer))[value] : 1-(*(monitor->atomic_prob_buffer))[value];
        break;
      case R2U2_FT_OP_SUBFORMULA: {
        r2u2_duoq_control_block_t* ctrl_child = &(arena->blocks[value]);
        result = (*(r2u2_probability*)&((ctrl_child->queue)[(rd_ptr) * (sizeof(r2u2_probability)/sizeof(r2u2_tnt_t))]));
        break;
      }
      case R2U2_FT_OP_NOT_SET:
        result = (r2u2_probability){0};
        break;
      default:
        R2U2_DEBUG_PRINT("Warning: Bad OP Type\n");
        result = (r2u2_probability){0};
        break;
    }
    return result;
}

#if R2U2_PRED_PROB
static r2u2_status_t push_result_probability(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_probability result) {
  // Pushes result to queue, sets tau, and flags progress if nedded
  r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
  r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);

  r2u2_duoq_ft_write_probability(arena, instr->memory_reference, result, monitor->predictive_mode);

  R2U2_DEBUG_PRINT("\t(%d,%f)\n", result.time, result.prob ); 

  ctrl->next_time = result.time + 1;

  // TODO(bckempa): Inline or macro this
  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

  return R2U2_OK;
}
#endif
static r2u2_status_t push_result(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr, r2u2_tnt_t result) {
  // Pushes result to queue, sets tau, and flags progress if nedded
  r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
  r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);

  r2u2_duoq_ft_write(arena, instr->memory_reference, result, monitor->predictive_mode);

  R2U2_DEBUG_PRINT("\t(%d,%s)\n", result & R2U2_TNT_TIME, (result & R2U2_TNT_TRUE) ? "T" : "F" );

  ctrl->next_time = (result & R2U2_TNT_TIME)+1;

  // TODO(bckempa): Inline or macro this
  if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}

  return R2U2_OK;
}

r2u2_status_t r2u2_mltl_ft_update(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t *instr) {

  #if R2U2_PRED_PROB
    r2u2_probability op0_prob, op1_prob, result_prob;
  #endif
  r2u2_bool op0_rdy, op1_rdy;
  r2u2_tnt_t op0, op1, result;
  r2u2_status_t error_cond;

  r2u2_duoq_arena_t *arena = &(monitor->duo_queue_mem);
  r2u2_duoq_control_block_t *ctrl = &(arena->blocks[instr->memory_reference]);
  r2u2_duoq_temporal_block_t *temp; // Only set this if using a temporal op
  #if R2U2_PRED_PROB
  r2u2_duoq_predict_block_t *predict; // Only set if using prediction
  #endif

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
        case R2U2_FT_OP_ATOMIC:
          r2u2_duoq_config(arena, instr->memory_reference, instr->op1_value, instr->op2_value);
          break;
        case R2U2_FT_OP_SUBFORMULA:
          r2u2_duoq_ft_temporal_config(arena, instr->memory_reference);
          temp = r2u2_duoq_ft_temporal_get(arena, instr->memory_reference);
          temp->lower_bound = instr->op1_value;
          temp->upper_bound = instr->op2_value;
          break;
        case R2U2_FT_OP_DIRECT:
          #if R2U2_PRED_PROB
          r2u2_duoq_ft_predict_config(arena, instr->memory_reference);
          predict = r2u2_duoq_ft_predict_get(arena, instr->memory_reference);
          predict->deadline = (r2u2_int)instr->op1_value;
          predict->k_modes = instr->op2_value;
          break;
          #endif
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

      #if R2U2_PRED_PROB
        if (ctrl->prob > 1.0){ // Indicates probabilistic operator
          if (check_operand_data_probability(monitor, instr, 0, &op0_prob)) {
            push_result_probability(monitor, instr, op0_prob);
          }
          error_cond = R2U2_OK;
          break;
        }
      #endif
      
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
        //ctrl->next_time = (op0 & R2U2_TNT_TIME)+1;
        push_result(monitor, instr, op0);

        if (monitor->out_file != NULL) {
          fprintf(monitor->out_file, "%d:%u,%s\n", instr->op2_value, (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE) ? "T" : "F");
        }

        if (monitor->out_func != NULL) {
          // TODO(bckempa): Migrate external function pointer interface to use r2u2_tnt_t
          (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &((r2u2_verdict){op0 & R2U2_TNT_TIME, (op0 & R2U2_TNT_TRUE) ? true : false}));
        }

        if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS) {monitor->progress = R2U2_MONITOR_PROGRESS_RELOOP_WITH_PROGRESS;}
        
      }

      #if R2U2_PRED_PROB
        // Multimodal Model Predictive Runtime Verification
        predict = r2u2_duoq_ft_predict_get(arena, instr->memory_reference);
        if (predict == NULL){
          error_cond = R2U2_OK;
          break;
        }
        if (monitor->progress == R2U2_MONITOR_PROGRESS_RELOOP_NO_PROGRESS){
          if((int)monitor->time_stamp - (int)predict->deadline >= 0){ // T_R - d >= 0
            r2u2_time index = monitor->time_stamp - predict->deadline;
            op0 = (ctrl->queue)[ctrl->write];
            if(op0 == r2u2_infinity || (op0 & R2U2_TNT_TIME) < index && ctrl->next_time <= index){ // last i produced < index; therefore, prediction required
              monitor->predictive_mode = true;
              r2u2_mltl_instruction_t* mltl_instructions[R2U2_MAX_INSTRUCTIONS];
              r2u2_bz_instruction_t* bz_instructions[R2U2_MAX_BZ_INSTRUCTIONS];
              r2u2_scq_state_t prev_real_state[R2U2_MAX_INSTRUCTIONS];
              r2u2_time k_trace_offset[predict->k_modes];
              r2u2_time k_prob_offset[predict->k_modes];
              size_t num_mltl_instructions, num_bz_instructions = 0;
              // Find child instructions for ft and booleanizer assembly (atomic checker not currently supported)
              r2u2_status_t status = find_child_instructions(monitor, &(*monitor->instruction_tbl)[monitor->prog_count], mltl_instructions, &num_mltl_instructions, 
                                                              bz_instructions, &num_bz_instructions, monitor->prog_count - instr->memory_reference);
              find_k_start_index(monitor, k_trace_offset, k_prob_offset, predict->k_modes);
              prep_prediction_scq(monitor, mltl_instructions, instr, prev_real_state, num_mltl_instructions);
              r2u2_signal_vector_t *signal_vector_original = monitor->signal_vector;
              r2u2_atomic_buffer_t *atomic_prob_buffer_original = monitor->atomic_prob_buffer;
              r2u2_time timestamp_original = monitor->time_stamp;

              r2u2_time iteration = 0;
              while(op0 == r2u2_infinity || (op0 & R2U2_TNT_TIME) < index){ // while prediction is required
                monitor->progress = R2U2_MONITOR_PROGRESS_FIRST_LOOP; // reset monitor state
                monitor->time_stamp++; // increment time step
                
                r2u2_float temp_prob_buffer[monitor->num_atomics];
                for(int j = 0; j < (int)predict->k_modes; j++){
                  monitor->signal_vector = &(*(signal_vector_original))[k_trace_offset[j]+(iteration*monitor->num_signals)];
                  monitor->atomic_prob_buffer = &(*(atomic_prob_buffer_original))[k_prob_offset[j]+(iteration*monitor->num_atomics)];
                  if(k_prob_offset[j] == 0 && predict->k_modes > 1){
                    for(int k = 0; k < monitor->num_atomics; k++){
                      (*(monitor->atomic_prob_buffer))[k] = 1.0 / predict->k_modes;
                    }
                  }
                  for(int i = num_bz_instructions - 1; i >= 0; i--){ // dispatch booleanizer instructions
                    R2U2_DEBUG_PRINT("%d.%d.%d.%d\n",monitor->time_stamp,iteration, i, j);
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
                    R2U2_DEBUG_PRINT("%d.%d.%d.%d\n",timestamp_original, iteration-1, i, monitor->progress);
                    r2u2_mltl_ft_update(monitor, mltl_instructions[i]);
                  }

                  R2U2_DEBUG_PRINT("%d.%d.%d.%d\n",timestamp_original, iteration-1, num_mltl_instructions, monitor->progress);
                  R2U2_DEBUG_PRINT("\tFT RETURN\n");
                  if(check_operand_data(monitor, instr, 0, &op0)){
                    // Only store result up to 'index'; don't predict for values after 'index'
                    result = min(index, op0 & R2U2_TNT_TIME) | (op0 & R2U2_TNT_TRUE);
                    push_result(monitor, instr, result);

                    if (monitor->out_file != NULL) {
                      fprintf(monitor->out_file, "%d:%u,%s (Predicted at time stamp %d)\n", instr->op2_value, (result & R2U2_TNT_TIME), (result & R2U2_TNT_TRUE) ? "T" : "F", timestamp_original);
                    }

                    if (monitor->out_func != NULL) {
                      // TODO(bckempa): Migrate external function pointer interface to use r2u2_tnt_t
                      (monitor->out_func)((r2u2_instruction_t){ R2U2_ENG_TL, instr}, &((r2u2_verdict){result & R2U2_TNT_TIME, (result & R2U2_TNT_TRUE) ? true : false}));
                    }
                    
                    if(min(index, op0 & R2U2_TNT_TIME) == index){
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
              monitor->time_stamp = timestamp_original;
            }
          }
        }
      #endif

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

      #if R2U2_PRED_PROB
      if(ctrl->prob > 1.0) { //Indicates probabilisitic operator
        if (check_operand_data_probability(monitor, instr, 0, &op0_prob)) {
          R2U2_DEBUG_PRINT("\tGot data\n");
          temp = r2u2_duoq_ft_temporal_get(arena, instr->memory_reference);
          if (op0_prob.time >= temp->upper_bound){
            r2u2_float p_temp = op0_prob.prob;
            R2U2_DEBUG_PRINT("\t\tp_temp = %lf\n", p_temp);
            r2u2_duoq_control_block_t *ctrl_child = &(arena->blocks[instr->op1_value]);
            for(int t = 1; t <= (temp->upper_bound-temp->lower_bound); t++){ //Iterate backwards through operand queue
              r2u2_time curr_index = ((int)ctrl->read1 - t < 0) ? (ctrl_child->length) + ((int)ctrl->read1 - t) : (ctrl->read1 - t);
              p_temp = p_temp * get_child_operand_probability(monitor, instr, 0, curr_index).prob;
              R2U2_DEBUG_PRINT("\t\tp_temp = p_temp * %lf = %lf\n", get_child_operand_probability(monitor, instr, 0, curr_index).prob, p_temp);
            }
            result_prob.time = op0_prob.time - temp->upper_bound;
            result_prob.prob = p_temp;
            push_result_probability(monitor, instr, result_prob);
          } else {
            R2U2_DEBUG_PRINT("\tWaiting...\n");
          }
          ctrl->next_time = op0_prob.time + 1;
        }
        error_cond = R2U2_OK;
        break;
      }
      #endif
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

      #if R2U2_PRED_PROB
        if(ctrl->prob > 1.0){ //Indicates probabilisitic operator
          if (check_operand_data_probability(monitor, instr, 0, &op0_prob) && check_operand_data_probability(monitor, instr, 1, &op1_prob)) {
            temp = r2u2_duoq_ft_temporal_get(arena, instr->memory_reference);
            // We need to see every timestep as an op0 op1 pair
            // both times should be equal at this point
            #if R2U2_DEBUG
              assert(op0_prob.time == op1_prob.time);
            #endif
            r2u2_time tau = min(op0_prob.time, op1_prob.time);            
            if (tau >= temp->upper_bound){
              r2u2_float p_temp = op1_prob.prob;
              R2U2_DEBUG_PRINT("p_temp = %lf\n", p_temp);
              r2u2_duoq_control_block_t *ctrl_child1 = &(arena->blocks[instr->op1_value]);
              r2u2_duoq_control_block_t *ctrl_child2 = &(arena->blocks[instr->op2_value]);
              for(int t = 1; t <= (temp->upper_bound-temp->lower_bound); t++){ //Iterate backwards through operand queue
                r2u2_time curr_index1 = ((int)ctrl->read1 - t < 0) ? (ctrl_child1->length) + ((int)ctrl->read1 - t) : (ctrl->read1 - t);
                r2u2_time curr_index2 = ((int)ctrl->read2 - t < 0) ? (ctrl_child2->length) + ((int)ctrl->read2 - t) : (ctrl->read2 - t);
                p_temp = p_temp * get_child_operand_probability(monitor, instr, 0, curr_index1).prob;
                R2U2_DEBUG_PRINT("p_temp = p_temp * %lf = %lf\n", get_child_operand_probability(monitor, instr, 0, curr_index1).prob, p_temp);
                p_temp = 1 - ((1 - get_child_operand_probability(monitor, instr, 1, curr_index2).prob)*(1 - p_temp));
                R2U2_DEBUG_PRINT("p_temp = 1 - ((1 - %lf) * (1 - p_temp)) = %lf\n", get_child_operand_probability(monitor, instr, 1, curr_index2).prob, p_temp);
              }
              result_prob.time = op0_prob.time - temp->upper_bound;
              result_prob.prob = p_temp;
              push_result_probability(monitor, instr, result_prob);
            }
            ctrl->next_time = tau+1;
          } else {
            R2U2_DEBUG_PRINT("\tWaiting...\n");
          }
          error_cond = R2U2_OK;
          break;
        }
      #endif
      if (check_operand_data(monitor, instr, 0, &op0) && check_operand_data(monitor, instr, 1, &op1)) {
        temp = r2u2_duoq_ft_temporal_get(arena, instr->memory_reference);
          // We need to see every timestep as an (op0, op1) pair
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
            R2U2_DEBUG_PRINT("\tWaiting...\n");
            error_cond = R2U2_OK;
            break;
          }

          // Didn't hit the else case above means we a result. If it is new, that
          // is the timestamp is grater than the one in temp->previous, we push.
          // We don't want to reset desired_time_stamp based on the result
          // so we reset `next_time` after we push to avoid one-off return logic.
          // To handle startup behavior, the truth bit of the previous result
          // storage is used to flag that an ouput has been produced, which can
          // differentate between a value of 0 for no output vs what would be 0
          // for an output of false at time 0. Since only the timestamp of the
          // previous result is ever checked, this overloading of the truth bit
          // doesn't cause confict with other logic and preserves startup
          // behavior when memory is nulled out
          R2U2_TRACE_PRINT("\tCandidate Result: (%d, %s)\n", (result & R2U2_TNT_TIME), (result & R2U2_TNT_TRUE) ? "T" : "F");
          R2U2_TRACE_PRINT("\t\tCheck 1: %d > %d == %d\n", (result & R2U2_TNT_TIME), (temp->previous & R2U2_TNT_TIME), ((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)));
          R2U2_TRACE_PRINT("\t\tCheck 2: %d && %d\n", ((result & R2U2_TNT_TIME) == 0), !(temp->previous & R2U2_TNT_TRUE));
          if (((result & R2U2_TNT_TIME) > (temp->previous & R2U2_TNT_TIME)) || \
              (((result & R2U2_TNT_TIME) == 0) && !(temp->previous & R2U2_TNT_TRUE))) {
            push_result(monitor, instr, result);
            ctrl->next_time = tau+1;
            temp->previous = R2U2_TNT_TRUE | result;
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

    /* Propositional Logic Observers */
    case R2U2_MLTL_OP_FT_NOT: {
      R2U2_DEBUG_PRINT("\tFT NOT\n");

      #if R2U2_PRED_PROB
        if (ctrl->prob > 1.0){ // Indicates probabilistic operator
          if (check_operand_data_probability(monitor, instr, 0, &op0_prob)) {
            op0_prob.prob = 1 - op0_prob.prob;
            push_result_probability(monitor, instr, op0_prob);
          }
          error_cond = R2U2_OK;
          break;
        }
      #endif
        if (check_operand_data(monitor, instr, 0, &op0)) {
          push_result(monitor, instr, op0 ^ R2U2_TNT_TRUE);
        }

      error_cond = R2U2_OK;
      break;
    }
    case R2U2_MLTL_OP_FT_AND: {
      R2U2_DEBUG_PRINT("\tFT AND\n");

      #if R2U2_PRED_PROB
        if (ctrl->prob > 1.0){ // Indicates probabilistic operator
          op0_rdy = check_operand_data_probability(monitor, instr, 0, &op0_prob);
          op1_rdy = check_operand_data_probability(monitor, instr, 1, &op1_prob);

          R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

          if (op0_rdy && op1_rdy) {
            result_prob.time = op0_prob.time;
            result_prob.prob = op0_prob.prob * op1_prob.prob;
            push_result_probability(monitor, instr, result_prob);
          }
          error_cond = R2U2_OK;
          break;
        }
      #endif

      op0_rdy = check_operand_data(monitor, instr, 0, &op0);
      op1_rdy = check_operand_data(monitor, instr, 1, &op1);

      R2U2_DEBUG_PRINT("\tData Ready: %d\t%d\n", op0_rdy, op1_rdy);

      if (op0_rdy && op1_rdy) {
        R2U2_DEBUG_PRINT("\tLeft & Right Ready: (%d, %s) (%d, %s)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE) ? "T" : "F", (op1 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TRUE) ? "T" : "F");
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
        R2U2_DEBUG_PRINT("\tOnly Left Ready: (%d, %s)\n", (op0 & R2U2_TNT_TIME), (op0 & R2U2_TNT_TRUE) ? "T" : "F");
        if(!(op0 & R2U2_TNT_TRUE)) {
          push_result(monitor, instr, (op0 & R2U2_TNT_TIME)| R2U2_TNT_FALSE);
        }
      } else if (op1_rdy) {
        R2U2_DEBUG_PRINT("\tOnly Right Ready: (%d, %s)\n", (op1 & R2U2_TNT_TIME), (op1 & R2U2_TNT_TRUE) ? "T" : "F");
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
    case R2U2_MLTL_OP_FT_PROB: {
      R2U2_DEBUG_PRINT("\tFT PROB\n");

      #if R2U2_PRED_PROB
        if (check_operand_data_probability(monitor, instr, 0, &op0_prob)) {
          R2U2_DEBUG_PRINT("\t\tProbability for i = %d is %f\n", op0_prob.time, op0_prob.prob);
          if(op0_prob.prob >= ctrl->prob)
            push_result(monitor, instr, (op0_prob.time & R2U2_TNT_TIME) |  R2U2_TNT_TRUE);
          else
            push_result(monitor, instr, (op0_prob.time & R2U2_TNT_TIME) |  R2U2_TNT_FALSE);
        }
      #endif
        error_cond = R2U2_OK;
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
