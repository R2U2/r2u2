use easy_min_max::{min, max};

use crate::instructions::mltl::*;
use crate::internals::{debug::*, types::*};
use crate::memory::{monitor::*,scq::*};

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

fn check_operand_data(instr: MLTLInstruction, monitor: &mut Monitor, op_num: u8) -> (bool, r2u2_verdict) {
    let operand_type = if op_num == 0 {instr.op1_type} else {instr.op2_type};
    let value = if op_num == 0 {instr.op1_value} else {instr.op2_value};

    match operand_type{
        MLTL_OP_TYPE_ATOMIC => {
            // Only load in atomics on first loop of time step
            return(monitor.progress == MonitorProgressState::FirstLoop, 
                r2u2_verdict{time: monitor.time_stamp, truth: monitor.atomic_buffer[value as usize]});
        }
        MLTL_OP_TYPE_DIRECT => {
            // Only directly load in T or F on first loop of time step
            return(monitor.progress == MonitorProgressState::FirstLoop, 
                r2u2_verdict{time: monitor.time_stamp, truth: value != 0});
        }
        MLTL_OP_TYPE_SUBFORMULA => {
            // Handled by the SCQ check function, just need to pass it the appropriate arguments
            let op_id = if op_num == 0 {instr.op1_value} else {instr.op2_value};
            return scq_read(monitor, instr.memory_reference, op_id, op_num);
        }
        MLTL_OP_TYPE_NOT_SET => {
            // Error
            return (false, r2u2_verdict::default());
        }
        _ => {
            // Error
            return (false, r2u2_verdict::default());
        }
    }
}

fn push_result(instr: MLTLInstruction, monitor: &mut Monitor, verdict: r2u2_verdict){
    let queue_ctrl = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
    
    queue_ctrl.next_time = verdict.time + 1;
    debug_print!("Desired time {}", queue_ctrl.next_time);

    if monitor.progress == MonitorProgressState::ReloopNoProgress {
        monitor.progress = MonitorProgressState::ReloopWithProgress;
    }

    scq_write(monitor, instr.memory_reference, verdict);
}

pub fn mltl_ft_update(monitor: &mut Monitor){
    let instr = monitor.mltl_instruction_table[monitor.mltl_program_count.curr_program_count];
    match instr.opcode {
        MLTL_OP_FT_NOP => {
            return;
        }
        MLTL_OP_FT_LOAD => {
            debug_print!("FT LOAD");
            let (ready, verdict) = check_operand_data(instr, monitor, 0);
            if ready {
                push_result(instr, monitor, verdict);
            }
        }
        MLTL_OP_FT_RETURN => {
            debug_print!("FT RETURN");
            let (ready, verdict) = check_operand_data(instr, monitor, 0);
            if ready {
                push_result(instr, monitor, verdict);
                debug_print!("{}:{},{}", instr.op2_value, verdict.time, if verdict.truth {"T"} else {"F"});
                monitor.output_buffer[monitor.output_buffer_idx] = r2u2_output{spec_num: instr.op2_value, verdict: verdict};
                monitor.output_buffer_idx += 1;
            }
        }
        MLTL_OP_FT_EVENTUALLY => {
            return;
        }
        MLTL_OP_FT_GLOBALLY => {
            debug_print!("FT GLOBAL");
            let (ready, op) = check_operand_data(instr, monitor, 0);
            if ready {
                let queue_ctrl = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
                // op compaction aware rising edge detection
                // To avoid reserving a null, sentinal, or "infinity" timestamp, we
                // also have to check for starting conditions.
                if op.truth && !queue_ctrl.temporal_block.previous.truth{
                    if queue_ctrl.next_time != 0 {
                        queue_ctrl.temporal_block.edge = queue_ctrl.temporal_block.previous.time+1;
                    } else {
                        queue_ctrl.temporal_block.edge = 0;
                    }
                    debug_print!("Rising edge at t={}", queue_ctrl.temporal_block.edge);
                }

                queue_ctrl.temporal_block.previous = op;

                let queue_ctrl = &monitor.queue_arena.control_blocks[instr.memory_reference as usize];

                if op.truth && queue_ctrl.temporal_block.edge != r2u2_infinity && 
                op.time >= queue_ctrl.temporal_block.upper_bound - queue_ctrl.temporal_block.lower_bound + queue_ctrl.temporal_block.edge &&
                op.time >= queue_ctrl.temporal_block.upper_bound {
                    debug_print!("Passed");
                    push_result(instr, monitor, r2u2_verdict{time: op.time - queue_ctrl.temporal_block.upper_bound, truth: true});
                } else if !op.truth && op.time >= queue_ctrl.temporal_block.lower_bound {
                    debug_print!("Desired time {}", queue_ctrl.next_time);
                    debug_print!("op.time - lower_bound: {} - {}", op.time, queue_ctrl.temporal_block.lower_bound);
                    push_result(instr, monitor, r2u2_verdict{time: op.time - queue_ctrl.temporal_block.lower_bound, truth: false});
                    debug_print!("Failed");
                }else{
                    debug_print!("Waiting");
                }
                let queue_ctrl = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
                queue_ctrl.next_time = op.time + 1;
            }
        }
        MLTL_OP_FT_UNTIL => {
            debug_print!("FT UNTIL");
            let (ready0, op0) = check_operand_data(instr, monitor, 0);
            let (ready1, op1) = check_operand_data(instr, monitor, 1);
            let mut result = r2u2_verdict::default();
            if ready0 && ready1 {
                let queue_ctrl = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
                // We need to see every timesetp as an (op0, op1) pair
                let tau = min!(op0.time, op1.time);
                queue_ctrl.next_time = tau + 1;
                
                if op1.truth {
                    queue_ctrl.temporal_block.edge = op1.time;
                }
                debug_print!("Time since right operand high: {}", tau - queue_ctrl.temporal_block.edge);

                if op1.truth && tau >= queue_ctrl.temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound{
                    debug_print!("Right Op True");
                    result.time = tau - queue_ctrl.temporal_block.lower_bound;
                    result.truth = true;
                } else if !op0.truth && tau >= queue_ctrl.temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound{
                    debug_print!("Left Op False");
                    result.time = tau - queue_ctrl.temporal_block.lower_bound;
                    result.truth = false;
                } else if tau >= queue_ctrl.temporal_block.upper_bound - queue_ctrl.temporal_block.lower_bound + queue_ctrl.temporal_block.edge &&
                tau >= queue_ctrl.temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound {
                    debug_print!("Time elapsed");
                    result.time = tau - queue_ctrl.temporal_block.upper_bound;
                    result.truth = false;
                } else {
                    debug_print!("Waiting");
                    return;
                }

                if result.time > queue_ctrl.temporal_block.previous.time ||
                (result.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                    queue_ctrl.next_time = tau + 1;
                    queue_ctrl.temporal_block.previous = r2u2_verdict{time: result.time, truth: true};
                    push_result(instr, monitor, result);
                }
            }
        }
        MLTL_OP_FT_RELEASE => {
            return;
        }
        MLTL_OP_FT_NOT => {
            debug_print!("FT NOT");
            let (ready, op) = check_operand_data(instr, monitor, 0);
            if ready {
                push_result(instr, monitor, r2u2_verdict{time: op.time, truth: !op.truth});
            }
        }
        MLTL_OP_FT_AND => {
            debug_print!("FT AND");
            let (ready0, op0) = check_operand_data(instr, monitor, 0);
            let (ready1, op1) = check_operand_data(instr, monitor, 1);
            if ready0 && ready1 {
                debug_print!("Left and Right Ready!");
                if op0.truth && op1.truth{
                    debug_print!("Both True");
                    push_result(instr, monitor, r2u2_verdict{time: min!(op0.time, op1.time), truth: true});
                }
                else if !op0.truth && !op1.truth {
                    debug_print!("Both False");
                    push_result(instr, monitor, r2u2_verdict{time: max!(op0.time, op1.time), truth: false});
                }
                else if op0.truth {
                    debug_print!("Only Left True");
                    push_result(instr, monitor, r2u2_verdict{time: op1.time, truth: false});
                }
                else if op1.truth{
                    debug_print!("Only Right True");
                    push_result(instr, monitor, r2u2_verdict{time: op0.time, truth: false});
                }
            }
            else if ready0 {
                debug_print!("Only Left Ready: ({},{})", op0.truth, op0.time);
                if !op0.truth{
                    push_result(instr, monitor, r2u2_verdict{time: op0.time, truth: false});
                }
            }
            else if ready1{
                debug_print!("Only Right Ready: ({},{})", op1.truth, op1.time);
                if !op1.truth{
                    push_result(instr, monitor, r2u2_verdict{time: op1.time, truth: false});
                }
            }
        }
        MLTL_OP_FT_OR => {
            return;
        }
        MLTL_OP_FT_IMPLIES => {
            return;
        }
        MLTL_OP_FT_PROB => {
            return;
        }
        MLTL_OP_FT_NOR => {
            return;
        }
        MLTL_OP_FT_XOR => {
            return;
        }
        MLTL_OP_FT_EQUIVALENT => {
            return;
        }
        _ => {
            return;
        }
    }
}