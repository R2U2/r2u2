#include "r2u2.h"
#include "prediction.h"
#include <stdlib.h>
#include <math.h>

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

void find_k_start_index(r2u2_monitor_t *monitor, r2u2_time* trace_start_index, r2u2_time* prob_start_index, size_t size){
  int temp1 = 0;
  int temp2 = 0;
  for(int i = 0; i < size; i++){
    while(true){
      if(strcmp((*(monitor->signal_vector))[temp1], "|") == 0){
        trace_start_index[i] = temp1+1;
        R2U2_DEBUG_PRINT("trace %d starts at %d\n", i, temp1+1);
        temp1 = temp1 + monitor->num_signals + 1;
        break;
      }
      else{
        temp1 = temp1 + monitor->num_signals;
      }
    }
    while(true){
      if((*(monitor->atomic_prob_buffer))[temp2] == 1000.0){
        prob_start_index[i] = temp2 + 1;
        R2U2_DEBUG_PRINT("probability trace %d starts at %d\n", i, temp2+1);
        temp2 = temp2 + monitor->num_atomics + 1;
        break;
      }
      else if((*(monitor->atomic_prob_buffer))[temp2] < 0){
        prob_start_index[i] = 0;
        break;
      }
      else{
        temp2 = temp2 + monitor->num_atomics;
      }
    }
  }
}

void prep_prediction_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_mltl_instruction_t* return_instr, r2u2_scq_state_t* prev_real_state, size_t size){
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
  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[return_instr->memory_reference]);
  prev_real_state[size].rd_ptr = scq->rd_ptr;
}

void restore_scq(r2u2_monitor_t *monitor, r2u2_mltl_instruction_t** instructions, r2u2_mltl_instruction_t* return_instr, r2u2_scq_state_t* prev_real_state, size_t size){
  for(size_t i = 0; i < size; i++){
      r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[instructions[i]->memory_reference]);
      scq->rd_ptr = prev_real_state[i].rd_ptr;
      scq->rd_ptr2 = prev_real_state[i].rd_ptr2;
      scq->desired_time_stamp = prev_real_state[i].desired_time_stamp;
      scq->edge = prev_real_state[i].edge;
      scq->max_out = prev_real_state[i].max_out;
      scq->previous = prev_real_state[i].previous;
  }
  r2u2_scq_t *scq = &(((r2u2_scq_t*)(*(monitor->future_time_queue_mem)))[return_instr->memory_reference]);
  scq->rd_ptr = prev_real_state[size].rd_ptr;
}