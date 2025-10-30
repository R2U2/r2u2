#[cfg(feature = "aux_string_specs")]
use fixedstr::ztr64;

use crate::instructions::mltl::*;
use crate::internals::types::*;
use crate::memory::{monitor::*,scq::*};

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
use crate::internals::debug::*;

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

use vstd::prelude::*;

verus! {

#[verifier::external]
fn check_operand_data(instr: MLTLInstruction, monitor: &mut Monitor, op_num: u8) -> Option<r2u2_verdict> {
    let operand_type = if op_num == 0 {instr.op1_type} else {instr.op2_type};
    let value = if op_num == 0 {instr.op1_value} else {instr.op2_value};

    match operand_type{
        MLTL_OP_TYPE_ATOMIC => {
            // Only load in atomics on first loop of time step
            if monitor.progress == MonitorProgressState::FirstLoop {
                return Some(r2u2_verdict{time: monitor.time_stamp, truth: monitor.atomic_buffer[value as usize]});
            }
        }
        MLTL_OP_TYPE_DIRECT => {
            if instr.opcode == MLTL_OP_SINCE || instr.opcode == MLTL_OP_TRIGGER {
                let queue_ctrl = monitor.queue_arena.control_blocks[instr.memory_reference as usize];
                return Some(r2u2_verdict{time: monitor.time_stamp.saturating_add(queue_ctrl.temporal_block.upper_bound), truth: value != 0});
            } else {
                return Some(r2u2_verdict{time: monitor.time_stamp, truth: value != 0});
            }
        }
        MLTL_OP_TYPE_SUBFORMULA => {
            // Handled by the SCQ check function, just need to pass it the appropriate arguments
            return scq_read(monitor, instr.memory_reference, value, op_num);
        }
        _ => {
            // Error
            return None;
        }
    }
    return None;
}

#[verifier::external]
fn push_result(instr: MLTLInstruction, monitor: &mut Monitor, verdict: r2u2_verdict){
    
    if monitor.progress == MonitorProgressState::ReloopNoProgress {
        monitor.progress = MonitorProgressState::ReloopWithProgress;
    }

    scq_write(monitor, instr.memory_reference, verdict);
}

#[verifier::external]
pub fn mltl_update(monitor: &mut Monitor){
    let instr = monitor.mltl_instruction_table[monitor.mltl_program_count.curr_program_count];
    match instr.opcode {
        MLTL_OP_LOAD => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("LOAD");
            let verdict = check_operand_data(instr, monitor, 0);
            if verdict.is_some() {
                let queue_ctrl = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
                queue_ctrl.next_time = verdict.unwrap().time.saturating_add(1);
                push_result(instr, monitor, verdict.unwrap());
            }
        }
        MLTL_OP_RETURN => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("RETURN");
            let verdict = check_operand_data(instr, monitor, 0);
            if verdict.is_some() {
                let queue_ctrl = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
                queue_ctrl.next_time = verdict.unwrap().time.saturating_add(1);
                // push_result(instr, monitor, verdict.unwrap());
                #[cfg(not(feature = "aux_string_specs"))]
                (monitor.output_buffer[monitor.output_buffer_idx] = r2u2_output{spec_num: instr.op2_value, verdict: verdict.unwrap()});
                #[cfg(all(any(feature = "debug_print_semihosting", feature = "debug_print_std"), not(feature="aux_string_specs")))]
                debug_print!("{}:{},{}", instr.op2_value, verdict.unwrap().time, if verdict.unwrap().truth {"T"} else {"F"});
                
                #[cfg(feature = "aux_string_specs")]
                // Set auxiliary data for function output
                if (instr.op2_value as usize) < monitor.formula_aux_string_table.len(){
                    monitor.output_buffer[monitor.output_buffer_idx] = r2u2_output{spec_num: instr.op2_value, spec_str: monitor.formula_aux_string_table[instr.op2_value as usize].spec_str, verdict: verdict.unwrap()};
                } else { // Reached end of aux_string_table
                    monitor.output_buffer[monitor.output_buffer_idx] = r2u2_output{spec_num: instr.op2_value, spec_str: ztr64::from(""), verdict: verdict.unwrap()};
                }
                #[cfg(all(any(feature = "debug_print_semihosting", feature = "debug_print_std"), feature = "aux_string_specs"))]
                debug_print!("{} ({}):{},{}",  monitor.output_buffer[monitor.output_buffer_idx].spec_str, instr.op2_value, verdict.unwrap().time, if verdict.unwrap().truth {"T"} else {"F"});
                
                monitor.output_buffer_idx += 1;
                #[cfg(feature = "aux_string_specs")]
                // Set auxiliary data for contract output
                for aux_data_idx in 0..monitor.contract_aux_string_table.len(){
                    if monitor.contract_aux_string_table[aux_data_idx].spec_str.is_empty() {
                        break; // Reached end of aux_string_table
                    }
                    if monitor.contract_aux_string_table[aux_data_idx].spec_0 == instr.op2_value && !verdict.unwrap().truth{ // AGC Inactive
                        monitor.contract_buffer[monitor.contract_buffer_idx] = r2u2_contract{spec_str: monitor.contract_aux_string_table[aux_data_idx].spec_str, time: verdict.unwrap().time, status: AGC_INACTIVE};
                        monitor.contract_buffer_idx += 1;
                        break;
                    } else if monitor.contract_aux_string_table[aux_data_idx].spec_1 == instr.op2_value && !verdict.unwrap().truth{ // AGC Invalid
                        monitor.contract_buffer[monitor.contract_buffer_idx] = r2u2_contract{spec_str: monitor.contract_aux_string_table[aux_data_idx].spec_str, time: verdict.unwrap().time, status: AGC_INVALID};
                        monitor.contract_buffer_idx += 1;
                        break;
                    } else if monitor.contract_aux_string_table[aux_data_idx].spec_2 == instr.op2_value && verdict.unwrap().truth{ // AGC Verified
                        monitor.contract_buffer[monitor.contract_buffer_idx] = r2u2_contract{spec_str: monitor.contract_aux_string_table[aux_data_idx].spec_str, time: verdict.unwrap().time, status: AGC_VERIFIED};
                        monitor.contract_buffer_idx += 1;
                        break;
                    }
                }
            }
        }
        MLTL_OP_EVENTUALLY => {
            return;
        }
        MLTL_OP_GLOBALLY => {
            return;
        }
        MLTL_OP_UNTIL => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("FT UNTIL");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            if let Some(result) = until_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        MLTL_OP_RELEASE => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("FT RELEASE");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            if let Some(result) = release_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        MLTL_OP_ONCE => {
            return;
        }
        MLTL_OP_HISTORICALLY => {
            return;
        }
        MLTL_OP_SINCE => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("PT SINCE");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            if let Some(result) = since_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        MLTL_OP_TRIGGER => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("PT TRIGGER");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            if let Some(result) = trigger_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        MLTL_OP_NOT => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("NOT");
            let op = check_operand_data(instr, monitor, 0);
            if let Some(result) = not_operator(op.is_some(), op.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        MLTL_OP_AND => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("AND");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            if let Some(result) = and_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        MLTL_OP_OR => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("OR");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            if let Some(result) = or_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        MLTL_OP_IMPLIES => {
            return;
        }
        MLTL_OP_PROB => {
            return;
        }
        MLTL_OP_XOR => {
            return;
        }
        MLTL_OP_EQUIVALENT => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("EQUIVALENT");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            if let Some(result) = equivalent_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]) { push_result(instr, monitor, result) }
        }
        _ => {
            return;
        }
    }
}

// Verus doesn't support saturating_sub; therefore, have to provide specification for it
pub open spec fn saturating_sub(lhs: r2u2_time, rhs: r2u2_time) -> r2u2_time {
    if lhs - rhs < 0 {
        0
    } else {
        (lhs - rhs) as r2u2_time
    }
}

#[allow(dead_code)]
#[verifier::external_fn_specification] // Verus doesn't support saturating_sub; therefore, have to provide specification for it
#[verifier::when_used_as_spec(saturating_sub)]
pub fn ex_saturating_sub(lhs: r2u2_time, rhs: r2u2_time) -> (result: r2u2_time)
    ensures
        result == saturating_sub(lhs, rhs)
{
    lhs.saturating_sub(rhs)
}

#[inline(always)]
pub fn min(op0: r2u2_time, op1: r2u2_time) -> (result: r2u2_time)
    ensures
        result == op0 || result == op1,
        op0 <= op1 ==> result == op0,
        op0 >= op1 ==> result == op1,
{
    if op0 < op1{
        return op0;
    } else {
        return op1;
    }
}

#[inline(always)]
pub fn max(op0: r2u2_time, op1: r2u2_time) -> (result: r2u2_time)
    ensures
        result == op0 || result == op1,
        op0 >= op1 ==> result == op0,
        op0 <= op1 ==> result == op1,
{
    if op0 > op1{
        return op0;
    } else {
        return op1;
    }
}

#[inline(always)]
fn until_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    requires 
        old(queue_ctrl).temporal_block.lower_bound <= old(queue_ctrl).temporal_block.upper_bound,
        old(queue_ctrl).next_time >= old(queue_ctrl).temporal_block.lower_bound,
        value_op0.time > old(queue_ctrl).temporal_block.previous.time + old(queue_ctrl).temporal_block.lower_bound ||
        (!old(queue_ctrl).temporal_block.previous.truth && value_op0.time >= old(queue_ctrl).temporal_block.lower_bound),
        value_op1.time > old(queue_ctrl).temporal_block.previous.time + old(queue_ctrl).temporal_block.lower_bound ||
        (!old(queue_ctrl).temporal_block.previous.truth && value_op1.time >= old(queue_ctrl).temporal_block.lower_bound),
    ensures        
        // previous always gets updated when a result is returned
        result.is_some() ==> queue_ctrl.temporal_block.previous.time == result.unwrap().time,
        result.is_none() ==> queue_ctrl.temporal_block.previous.time == old(queue_ctrl).temporal_block.previous.time,
        
        // results are strictly increasing
        result.is_some() ==> (result.unwrap().time > old(queue_ctrl).temporal_block.previous.time || 
        (!old(queue_ctrl).temporal_block.previous.truth)),
        result.is_some() ==> queue_ctrl.temporal_block.previous.truth,
        
        // if op1 is true, then the result is true
        (ready_op1 && value_op1.truth && result.is_some()) ==> result.unwrap().truth,
        
        // if op0 and op1 are false, then the result is false
        (ready_op0 && !value_op0.truth && !value_op1.truth && result.is_some()) ==> !result.unwrap().truth,

        // if op1 is false, then the result is false
        (ready_op1 && !value_op1.truth && result.is_some()) ==> !result.unwrap().truth,
        
        // result timestamp is restricted by the timestamp of op0, op1, lb, and ub
        result.is_some() ==> (result.unwrap().time == value_op0.time - queue_ctrl.temporal_block.lower_bound || 
            result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.lower_bound || 
            result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.upper_bound),

        // queue_ctrl.next time doesn't change when neither side is ready or when we cannot evaluate early based on the rhs alone
        (!ready_op0 && !ready_op1) || (!ready_op0 && ready_op1 && result.is_none()) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

        // rhs true
        (ready_op1 && value_op1.truth && 
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound) ==>
            (result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op1 && value_op1.truth && 
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound &&
            value_op1.time - queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        
        // lhs false before rhs true post-conditions
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth && value_op0.time <= value_op1.time &&
            value_op0.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound) ==>
            (!result.unwrap().truth && result.unwrap().time == value_op0.time - queue_ctrl.temporal_block.lower_bound &&
            (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth && value_op0.time <= value_op1.time &&
            value_op0.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound &&
            value_op0.time - queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (!result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
            (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth && value_op0.time >= value_op1.time &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound) ==>
            (!result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.lower_bound &&
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth && value_op0.time >= value_op1.time &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound &&
            value_op1.time - queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (!result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // rhs false for entire [lb,ub] interval post-conditions
        (!ready_op0 && ready_op1 && !value_op1.truth &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound) ==>
            (!result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.upper_bound &&
            (queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 ||
                queue_ctrl.next_time == old(queue_ctrl).next_time ||
                queue_ctrl.next_time == r2u2_time::MAX)),
        (!ready_op0 && ready_op1 && !value_op1.truth &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound &&
            value_op1.time - queue_ctrl.temporal_block.upper_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (!result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet                  
            (queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 || 
                queue_ctrl.next_time == old(queue_ctrl).next_time ||
                queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound) ==>
            (!result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.upper_bound &&
            ((value_op0.time < value_op1.time && (
                (value_op0.time >= value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op0.time + 1) || 
                (value_op0.time < value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1))) || 
            (value_op0.time >= value_op1.time && queue_ctrl.next_time == value_op1.time + 1) ||
                queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound &&
            value_op1.time - queue_ctrl.temporal_block.upper_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (!result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet                  
            ((value_op0.time < value_op1.time && (
                (value_op0.time >= value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op0.time + 1) || 
                (value_op0.time < value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1))) || 
            (value_op0.time >= value_op1.time && queue_ctrl.next_time == value_op1.time + 1) ||
                queue_ctrl.next_time == r2u2_time::MAX)),

        // not enough information to produce result
        (ready_op0 && !ready_op1) ==> result.is_none() && old(queue_ctrl).next_time == queue_ctrl.next_time,
        (!ready_op0 && !ready_op1) ==> result.is_none() && old(queue_ctrl).next_time == queue_ctrl.next_time,
        (ready_op0 && ready_op1 && value_op0.truth && !value_op1.truth &&
            value_op1.time < old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound && 
                old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound <= r2u2_time::MAX) ==> 
                result.is_none() && ((value_op0.time < value_op1.time && queue_ctrl.next_time == value_op0.time + 1) || 
                (value_op0.time >= value_op1.time && queue_ctrl.next_time == value_op1.time + 1) || queue_ctrl.next_time == r2u2_time::MAX),
        (!ready_op0 && !value_op1.truth &&
            value_op1.time < old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound && 
                old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound <= r2u2_time::MAX) ==> result.is_none() && old(queue_ctrl).next_time == queue_ctrl.next_time
{
    let mut verdict = r2u2_verdict::default();
    if ready_op1 {
        // If op1 is true at lb, then true
        if value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Right Op True");
            verdict.time = value_op1.time - queue_ctrl.temporal_block.lower_bound;
            verdict.truth = true;
            
            queue_ctrl.next_time = value_op1.time.saturating_add(1);
            queue_ctrl.temporal_block.previous = verdict;
            return Some(verdict);
        }
        if ready_op0 {
            // We need to see every timestep as an (op0, op1) pair if op0 is required for evaluation
            let tau = min(value_op0.time, value_op1.time);
            queue_ctrl.next_time = tau.saturating_add(1); // Only need to see each timestep pair once

                if !value_op0.truth { // if op0 and op1 false, then false
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("Left and Right Op False");
                    verdict.time = tau - queue_ctrl.temporal_block.lower_bound;
                    verdict.truth = false;

                    queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                    return Some(verdict);
                }
        }
        // if op1 is false the entire interval [lb, ub], then false
        if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_add(queue_ctrl.temporal_block.upper_bound){
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Right Op False and Time elapsed");
            verdict.time = value_op1.time - queue_ctrl.temporal_block.upper_bound;
            verdict.truth = false;

            // To handle startup behavior, the truth bit of the previous result
            // storage is used to flag that an ouput has been produced, which can
            // differentiate between a value of 0 for no output vs output produced.
            // Note: Since only the timestamp of the previous result is ever checked,
            // this overloading of the truth bit doesn't cause confict with other logic 
            // and preserves startup behavior.
            if verdict.time > queue_ctrl.temporal_block.previous.time ||
            (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                queue_ctrl.next_time = max(queue_ctrl.next_time, verdict.time.saturating_add(queue_ctrl.temporal_block.lower_bound).saturating_add(1));
                queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                return Some(verdict);
            }
        }
    }
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn release_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    requires 
        old(queue_ctrl).temporal_block.lower_bound <= old(queue_ctrl).temporal_block.upper_bound,
        old(queue_ctrl).next_time >= old(queue_ctrl).temporal_block.lower_bound,
        value_op0.time > old(queue_ctrl).temporal_block.previous.time + old(queue_ctrl).temporal_block.lower_bound ||
        (!old(queue_ctrl).temporal_block.previous.truth && value_op0.time >= old(queue_ctrl).temporal_block.lower_bound),
        value_op1.time > old(queue_ctrl).temporal_block.previous.time + old(queue_ctrl).temporal_block.lower_bound ||
        (!old(queue_ctrl).temporal_block.previous.truth && value_op1.time >= old(queue_ctrl).temporal_block.lower_bound),
    ensures        
        // previous always gets updated when a result is returned
        result.is_some() ==> queue_ctrl.temporal_block.previous.time == result.unwrap().time,
        result.is_none() ==> queue_ctrl.temporal_block.previous.time == old(queue_ctrl).temporal_block.previous.time,
        
        // results are strictly increasing
        result.is_some() ==> (result.unwrap().time > old(queue_ctrl).temporal_block.previous.time || 
        (!old(queue_ctrl).temporal_block.previous.truth)),
        result.is_some() ==> queue_ctrl.temporal_block.previous.truth,
        
        // if op1 is false, then the result is false
        (ready_op1 && !value_op1.truth && result.is_some()) ==> !result.unwrap().truth,
        
        // if op0 and op1 are true, then the result is true
        (ready_op0 && value_op0.truth && value_op1.truth && result.is_some()) ==> result.unwrap().truth,

        // if op1 is true, then the result is true
        (ready_op1 && value_op1.truth && result.is_some()) ==> result.unwrap().truth,
        
        // result timestamp is restricted by the timestamp of op0, op1, lb, and ub
        result.is_some() ==> (result.unwrap().time == value_op0.time - queue_ctrl.temporal_block.lower_bound || 
            result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.lower_bound || 
            result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.upper_bound),

        // queue_ctrl.next time doesn't change when neither side is ready or when we cannot evaluate early based on the rhs alone
        (!ready_op0 && !ready_op1) || (!ready_op0 && ready_op1 && result.is_none()) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

        // rhs false
        (ready_op1 && !value_op1.truth && 
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound) ==>
            (!result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op1 && !value_op1.truth && 
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound &&
            value_op1.time - queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (!result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        
        // lhs true and rhs true
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth && value_op0.time <= value_op1.time &&
            value_op0.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound) ==>
            (result.unwrap().truth && result.unwrap().time == value_op0.time - queue_ctrl.temporal_block.lower_bound &&
            (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth && value_op0.time <= value_op1.time &&
            value_op0.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound &&
            value_op0.time - queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
            (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth && value_op0.time >= value_op1.time &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound) ==>
            (result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.lower_bound &&
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth && value_op0.time >= value_op1.time &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.lower_bound &&
            value_op1.time - queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // // rhs true for entire [lb,ub] interval post-conditions
        (!ready_op0 && ready_op1 && value_op1.truth &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound) ==>
            (result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.upper_bound &&
            (queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 ||
                queue_ctrl.next_time == old(queue_ctrl).next_time ||
                queue_ctrl.next_time == r2u2_time::MAX)),
        (!ready_op0 && ready_op1 && value_op1.truth &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound &&
            value_op1.time - queue_ctrl.temporal_block.upper_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet                  
            (queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 || 
                queue_ctrl.next_time == old(queue_ctrl).next_time ||
                queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && value_op1.truth &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound) ==>
            (result.unwrap().truth && result.unwrap().time == value_op1.time - queue_ctrl.temporal_block.upper_bound &&
            ((value_op0.time < value_op1.time && (
                (value_op0.time >= value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op0.time + 1) || 
                (value_op0.time < value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1))) || 
            (value_op0.time >= value_op1.time && queue_ctrl.next_time == value_op1.time + 1) ||
                queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && value_op1.truth &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound &&
            value_op1.time - queue_ctrl.temporal_block.upper_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) ==>
            (result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet                  
            ((value_op0.time < value_op1.time && (
                (value_op0.time >= value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op0.time + 1) || 
                (value_op0.time < value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1 && queue_ctrl.next_time == value_op1.time - queue_ctrl.temporal_block.upper_bound + queue_ctrl.temporal_block.lower_bound + 1))) || 
            (value_op0.time >= value_op1.time && queue_ctrl.next_time == value_op1.time + 1) ||
                queue_ctrl.next_time == r2u2_time::MAX)),

        // not enough information to produce result
        (ready_op0 && !ready_op1) ==> result.is_none() && old(queue_ctrl).next_time == queue_ctrl.next_time,
        (!ready_op0 && !ready_op1) ==> result.is_none() && old(queue_ctrl).next_time == queue_ctrl.next_time,
        (ready_op0 && ready_op1 && !value_op0.truth && value_op1.truth &&
            value_op1.time < old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound && 
                old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound <= r2u2_time::MAX) ==> 
                result.is_none() && ((value_op0.time < value_op1.time && queue_ctrl.next_time == value_op0.time + 1) || 
                (value_op0.time >= value_op1.time && queue_ctrl.next_time == value_op1.time + 1) || queue_ctrl.next_time == r2u2_time::MAX),
        (!ready_op0 && value_op1.truth &&
            value_op1.time < old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound && 
                old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound <= r2u2_time::MAX) ==> result.is_none() && old(queue_ctrl).next_time == queue_ctrl.next_time
{
    let mut verdict = r2u2_verdict::default();
    if ready_op1 {
        // If op1 is false at lb, then false
        if !value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Right Op False");
            verdict.time = value_op1.time - queue_ctrl.temporal_block.lower_bound;
            verdict.truth = false;
            
            queue_ctrl.next_time = value_op1.time.saturating_add(1);
            queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
            return Some(verdict);
        }
        if ready_op0 {
            // We need to see every timestep as an (op0, op1) pair if op0 is required for evaluation
            let tau = min(value_op0.time, value_op1.time);
            queue_ctrl.next_time = tau.saturating_add(1); // Only need to see each timestep pair once

                if value_op0.truth { // if op0 and op1 true, then true
                #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                debug_print!("Left and Right Op True");
                    verdict.time = tau - queue_ctrl.temporal_block.lower_bound;
                    verdict.truth = true;

                    queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                    return Some(verdict);
                }
        }
        // if op1 is false the entire interval [lb, ub], then false
        if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_add(queue_ctrl.temporal_block.upper_bound){
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Right Op True and Time elapsed");
            verdict.time = value_op1.time - queue_ctrl.temporal_block.upper_bound;
            verdict.truth = true;

            // To handle startup behavior, the truth bit of the previous result
            // storage is used to flag that an ouput has been produced, which can
            // differentiate between a value of 0 for no output vs output produced.
            // Note: Since only the timestamp of the previous result is ever checked,
            // this overloading of the truth bit doesn't cause confict with other logic 
            // and preserves startup behavior.
            if verdict.time > queue_ctrl.temporal_block.previous.time ||
            (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                queue_ctrl.next_time = max(queue_ctrl.next_time, verdict.time.saturating_add(queue_ctrl.temporal_block.lower_bound).saturating_add(1));
                queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                return Some(verdict);
            }
        }
    }
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn since_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    requires 
        old(queue_ctrl).temporal_block.lower_bound <= old(queue_ctrl).temporal_block.upper_bound,
        ready_op0 ==> value_op0.time >= old(queue_ctrl).next_time,
        ready_op1 ==> value_op1.time >= old(queue_ctrl).next_time,
    ensures        
        // previous always gets updated when a result is returned
        result.is_some() ==> queue_ctrl.temporal_block.previous.time == result.unwrap().time,
        result.is_none() ==> queue_ctrl.temporal_block.previous.time == old(queue_ctrl).temporal_block.previous.time,

        // results are strictly increasing
        result.is_some() ==> (result.unwrap().time > old(queue_ctrl).temporal_block.previous.time || 
        (!old(queue_ctrl).temporal_block.previous.truth)),
        result.is_some() ==> queue_ctrl.temporal_block.previous.truth,

        // if op1 is true, then the result is true
        (ready_op1 && value_op1.truth && (queue_ctrl.temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) && result.is_some()) ==> result.unwrap().truth,

        // if op0 and op1 are false, then the result is false
        (ready_op0 && !value_op0.truth && !value_op1.truth && result.is_some()) ==> !result.unwrap().truth,

        // if op1 is true, update edge and next time
        (ready_op1 && value_op1.truth && (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0)) ==> 
            ((queue_ctrl.temporal_block.edge.time == value_op1.time && queue_ctrl.temporal_block.edge.truth) &&
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // result timestamp is restricted by the timestamp of op0, op1, edge, lb, and ub
        result.is_some() ==> (result.unwrap().time == queue_ctrl.temporal_block.lower_bound - 1 ||
            result.unwrap().time == value_op0.time + queue_ctrl.temporal_block.lower_bound || 
            result.unwrap().time == queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound || 
            result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound ||
            result.unwrap().time == r2u2_time::MAX),

        // False for [0,lb-1] when 0-lb < 0
        (queue_ctrl.temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound < 0) && result.is_some() ==> 
            !result.unwrap().truth && result.unwrap().time == queue_ctrl.temporal_block.lower_bound - 1,

        // rhs true at i - lb
        ((ready_op1 && value_op1.truth && 
            (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound) &&
            value_op1.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> result.unwrap().truth && (result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound || result.unwrap().time == r2u2_time::MAX) &&
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        ((ready_op1 && value_op1.truth && 
            (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound) &&
            value_op1.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) 
            ==> result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),

        // rhs false from [i-ub,i-lb]
        (ready_op1 && !value_op1.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (!queue_ctrl.temporal_block.edge.truth || queue_ctrl.temporal_block.edge.time <= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> !result.unwrap().truth && (result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound || result.unwrap().time == r2u2_time::MAX) &&
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        (ready_op1 && !value_op1.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (!queue_ctrl.temporal_block.edge.truth || queue_ctrl.temporal_block.edge.time <= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth)
            ==> !result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        
        // rhs false after i-ub and lhs was never true from previous rhs to i - ub
        (ready_op1 && !value_op1.truth && ready_op0 && !value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> !result.unwrap().truth && (result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound || result.unwrap().time == r2u2_time::MAX) &&
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        (ready_op1 && !value_op1.truth && ready_op0 && !value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth)
            ==> !result.unwrap().truth && (result.unwrap().time == 0) && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),

        // lhs true from rhs to i-ub
        ((!ready_op1 || (ready_op1 && !value_op1.truth) || (ready_op1 && value_op1.time < old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound)) &&
            ready_op0 && value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op0.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op0.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> result.unwrap().truth && 
                ((value_op0.time + queue_ctrl.temporal_block.lower_bound >= queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound && result.unwrap().time == queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound && 
                        (queue_ctrl.next_time == queue_ctrl.temporal_block.edge.time + 1 || queue_ctrl.next_time == r2u2_time::MAX || queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == old(queue_ctrl).next_time)) ||
                (value_op0.time + queue_ctrl.temporal_block.lower_bound < queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound && result.unwrap().time == value_op0.time + queue_ctrl.temporal_block.lower_bound && 
                        (queue_ctrl.next_time == value_op0.time + queue_ctrl.temporal_block.lower_bound - queue_ctrl.temporal_block.upper_bound + 1 || queue_ctrl.next_time == 1 || queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == old(queue_ctrl).next_time)) ||
                result.unwrap().time == r2u2_time::MAX),

        ((!ready_op1 || (ready_op1 && !value_op1.truth) || (ready_op1 && value_op1.time < old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound)) &&
            ready_op0 && value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op0.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op0.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth)
            ==> result.unwrap().truth && (result.unwrap().time == 0) && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                queue_ctrl.next_time == 1,
            
        // not enough information to produce result
        (!ready_op0 || value_op0.time < old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound) &&
        (!ready_op1 || value_op1.time < old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound) &&
        (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) ==> result.is_none(),

        // not enough information to produce result; lhs true from rhs but not to i-ub
        (ready_op1 && !value_op1.truth && value_op1.time >= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound &&
            ready_op0 && value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op0.time < old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && (queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound)))
            ==> result.is_none(),
    
        // not enough information to produce result; rhs less than i-ub and currently no edge
        ((!ready_op1 || (ready_op1 && value_op1.time < old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound)) &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            queue_ctrl.temporal_block.edge.time > 0 &&
            (!queue_ctrl.temporal_block.edge.truth || queue_ctrl.temporal_block.edge.time <= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound))
            ==> result.is_none()
        
{
    if !queue_ctrl.temporal_block.previous.truth && queue_ctrl.temporal_block.previous.time < queue_ctrl.temporal_block.lower_bound{
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Not enough data to evaluate at beginning of trace");
        queue_ctrl.temporal_block.previous = r2u2_verdict{time: queue_ctrl.temporal_block.lower_bound - 1, truth: true};
        return Some(r2u2_verdict{time: queue_ctrl.temporal_block.previous.time, truth: false});
    }
    let mut verdict = r2u2_verdict::default();
    if ready_op1 {
        if value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("New edge: {}", value_op1.time);
            queue_ctrl.temporal_block.edge = r2u2_verdict{time: value_op1.time, truth: true};
            queue_ctrl.next_time = value_op1.time.saturating_add(1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Right Op True");
            if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound){
                verdict.time = value_op1.time.saturating_add(queue_ctrl.temporal_block.lower_bound);
                verdict.truth = true;
    
                // To handle startup behavior, the truth bit of the previous result
                // storage is used to flag that an ouput has been produced, which can
                // differentiate between a value of 0 for no output vs output produced.
                // Note: Since only the timestamp of the previous result is ever checked,
                // this overloading of the truth bit doesn't cause confict with other logic 
                // and preserves startup behavior.
                if verdict.time > queue_ctrl.temporal_block.previous.time ||
                (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("Right Op True at i-lb");
                    queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                    return Some(verdict);
                }
            }
        } else {
            let start_interval = queue_ctrl.temporal_block.previous.time.checked_sub(queue_ctrl.temporal_block.upper_bound);
            if !queue_ctrl.temporal_block.edge.truth || (start_interval.is_some() && queue_ctrl.temporal_block.edge.time <= start_interval.unwrap_or(0)){
                queue_ctrl.next_time = value_op1.time.saturating_add(1);
                if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound) {
                    verdict.time = value_op1.time.saturating_add(queue_ctrl.temporal_block.lower_bound);
                    verdict.truth = false;
                    if verdict.time > queue_ctrl.temporal_block.previous.time ||
                    (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                        debug_print!("Right Op never true from [i-ub, i-lb]");
                        queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                        return Some(verdict);
                    }
                }
            }
            if ready_op0 && !value_op0.truth {
                queue_ctrl.next_time = value_op1.time.saturating_add(1);
                if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound){
                    verdict.time = value_op1.time.saturating_add(queue_ctrl.temporal_block.lower_bound);
                    verdict.truth = false;

                    if verdict.time > queue_ctrl.temporal_block.previous.time ||
                    (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                        debug_print!("Both False");
                        queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                        return Some(verdict);
                    }
                }
            }
        }
    }
    let start_interval = queue_ctrl.temporal_block.previous.time.checked_sub(queue_ctrl.temporal_block.upper_bound);
    if ready_op0 && value_op0.truth && value_op0.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound) &&
        ((queue_ctrl.temporal_block.edge.truth) && (start_interval.is_none() || queue_ctrl.temporal_block.edge.time > start_interval.unwrap_or(0))){
        verdict.time = min(value_op0.time.saturating_add(queue_ctrl.temporal_block.lower_bound), queue_ctrl.temporal_block.edge.time.saturating_add(queue_ctrl.temporal_block.upper_bound));
        verdict.truth = true;

        if verdict.time > queue_ctrl.temporal_block.previous.time ||
        (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Left Op True Since Right Op True");
            queue_ctrl.next_time = max(queue_ctrl.next_time, verdict.time.saturating_sub(queue_ctrl.temporal_block.upper_bound).saturating_add(1));
            queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
            return Some(verdict);
        }
    }
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn trigger_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    requires 
        old(queue_ctrl).temporal_block.lower_bound <= old(queue_ctrl).temporal_block.upper_bound,
        ready_op0 ==> value_op0.time >= old(queue_ctrl).next_time,
        ready_op1 ==> value_op1.time >= old(queue_ctrl).next_time,
    ensures        
        // previous always gets updated when a result is returned
        result.is_some() ==> queue_ctrl.temporal_block.previous.time == result.unwrap().time,
        result.is_none() ==> queue_ctrl.temporal_block.previous.time == old(queue_ctrl).temporal_block.previous.time,

        // results are strictly increasing
        result.is_some() ==> (result.unwrap().time > old(queue_ctrl).temporal_block.previous.time || 
        (!old(queue_ctrl).temporal_block.previous.truth)),
        result.is_some() ==> queue_ctrl.temporal_block.previous.truth,

        // if op1 is false, then the result is false
        (ready_op1 && !value_op1.truth && (queue_ctrl.temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) && result.is_some()) ==> !result.unwrap().truth,

        // if op0 and op1 are true, then the result is true
        (ready_op0 && value_op0.truth && value_op1.truth && result.is_some()) ==> result.unwrap().truth,

        // if op1 is false, update edge and next time
        (ready_op1 && !value_op1.truth && (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0)) ==> 
            ((queue_ctrl.temporal_block.edge.time == value_op1.time && queue_ctrl.temporal_block.edge.truth) &&
            (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // result timestamp is restricted by the timestamp of op0, op1, edge, lb, and ub
        result.is_some() ==> (result.unwrap().time == queue_ctrl.temporal_block.lower_bound - 1 ||
            result.unwrap().time == value_op0.time + queue_ctrl.temporal_block.lower_bound || 
            result.unwrap().time == queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound || 
            result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound ||
            result.unwrap().time == r2u2_time::MAX),

        // True for [0,lb-1] when 0-lb < 0
        (queue_ctrl.temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound < 0) && result.is_some() ==> 
            result.unwrap().truth && result.unwrap().time == queue_ctrl.temporal_block.lower_bound - 1,

        // rhs false at i - lb
        ((ready_op1 && !value_op1.truth && 
            (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound) &&
            value_op1.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> !result.unwrap().truth && (result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound || result.unwrap().time == r2u2_time::MAX) &&
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        ((ready_op1 && !value_op1.truth && 
            (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound) &&
            value_op1.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth) 
            ==> !result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),

        // rhs true from [i-ub,i-lb]
        (ready_op1 && value_op1.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (!queue_ctrl.temporal_block.edge.truth || queue_ctrl.temporal_block.edge.time <= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> result.unwrap().truth && (result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound || result.unwrap().time == r2u2_time::MAX) &&
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        (ready_op1 && value_op1.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (!queue_ctrl.temporal_block.edge.truth || queue_ctrl.temporal_block.edge.time <= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth)
            ==> result.unwrap().truth && result.unwrap().time == 0 && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        
        // rhs true after i-ub and lhs was never false from previous rhs to i - ub
        (ready_op1 && value_op1.truth && ready_op0 && value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> result.unwrap().truth && (result.unwrap().time == value_op1.time + queue_ctrl.temporal_block.lower_bound || result.unwrap().time == r2u2_time::MAX) &&
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),
        (ready_op1 && value_op1.truth && ready_op0 && value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op1.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op1.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth)
            ==> result.unwrap().truth && (result.unwrap().time == 0) && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX),

        // lhs false from rhs to i-ub
        ((!ready_op1 || (ready_op1 && value_op1.truth) || (ready_op1 && value_op1.time < old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound)) &&
            ready_op0 && !value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op0.time > old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op0.time + queue_ctrl.temporal_block.lower_bound <= r2u2_time::MAX)
            ==> !result.unwrap().truth && 
                ((value_op0.time + queue_ctrl.temporal_block.lower_bound >= queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound && result.unwrap().time == queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound && 
                        (queue_ctrl.next_time == queue_ctrl.temporal_block.edge.time + 1 || queue_ctrl.next_time == r2u2_time::MAX || queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == old(queue_ctrl).next_time)) ||
                (value_op0.time + queue_ctrl.temporal_block.lower_bound < queue_ctrl.temporal_block.edge.time + queue_ctrl.temporal_block.upper_bound && result.unwrap().time == value_op0.time + queue_ctrl.temporal_block.lower_bound && 
                        (queue_ctrl.next_time == value_op0.time + queue_ctrl.temporal_block.lower_bound - queue_ctrl.temporal_block.upper_bound + 1 || queue_ctrl.next_time == 1 || queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == old(queue_ctrl).next_time)) ||
                result.unwrap().time == r2u2_time::MAX),

        ((!ready_op1 || (ready_op1 && value_op1.truth) || (ready_op1 && value_op1.time < old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound)) &&
            ready_op0 && !value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op0.time == old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound) && 
            value_op0.time + queue_ctrl.temporal_block.lower_bound == 0 && !old(queue_ctrl).temporal_block.previous.truth)
            ==> !result.unwrap().truth && (result.unwrap().time == 0) && // Initial case where previous = 0 but no output was produced at timestamp 0 yet
                queue_ctrl.next_time == 1,
            
        // not enough information to produce result
        (!ready_op0 || value_op0.time < old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound) &&
        (!ready_op1 || value_op1.time < old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound) &&
        (old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0) ==> result.is_none(),

        // not enough information to produce result; lhs false from rhs but not to i-ub
        (ready_op1 && value_op1.truth && value_op1.time >= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound &&
            ready_op0 && !value_op0.truth &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            value_op0.time < old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound && 
            (queue_ctrl.temporal_block.edge.truth && (queue_ctrl.temporal_block.edge.time > old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound)))
            ==> result.is_none(),
    
        // not enough information to produce result; rhs less than i-ub and currently no edge
        ((!ready_op1 || (ready_op1 && value_op1.time < old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.lower_bound)) &&
            old(queue_ctrl).temporal_block.previous.time-queue_ctrl.temporal_block.lower_bound >= 0 &&
            queue_ctrl.temporal_block.edge.time > 0 &&
            (!queue_ctrl.temporal_block.edge.truth || queue_ctrl.temporal_block.edge.time <= old(queue_ctrl).temporal_block.previous.time - queue_ctrl.temporal_block.upper_bound))
            ==> result.is_none()
        
{
    if !queue_ctrl.temporal_block.previous.truth && queue_ctrl.temporal_block.previous.time < queue_ctrl.temporal_block.lower_bound{
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Not enough data to evaluate at beginning of trace");
        queue_ctrl.temporal_block.previous = r2u2_verdict{time: queue_ctrl.temporal_block.lower_bound - 1, truth: true};
        return Some(r2u2_verdict{time: queue_ctrl.temporal_block.previous.time, truth: true});
    }
    let mut verdict = r2u2_verdict::default();
    if ready_op1 {
        if !value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("New edge: {}", value_op1.time);
            queue_ctrl.temporal_block.edge = r2u2_verdict{time: value_op1.time, truth: true};
            queue_ctrl.next_time = value_op1.time.saturating_add(1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Right Op False");
            if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound){
                verdict.time = value_op1.time.saturating_add(queue_ctrl.temporal_block.lower_bound);
                verdict.truth = false;
    
                // To handle startup behavior, the truth bit of the previous result
                // storage is used to flag that an ouput has been produced, which can
                // differentiate between a value of 0 for no output vs output produced.
                // Note: Since only the timestamp of the previous result is ever checked,
                // this overloading of the truth bit doesn't cause confict with other logic 
                // and preserves startup behavior.
                if verdict.time > queue_ctrl.temporal_block.previous.time ||
                (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("Right Op False at i-lb");
                    queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                    return Some(verdict);
                }
            }
        } else {
            let start_interval = queue_ctrl.temporal_block.previous.time.checked_sub(queue_ctrl.temporal_block.upper_bound);
            if !queue_ctrl.temporal_block.edge.truth || (start_interval.is_some() && queue_ctrl.temporal_block.edge.time <= start_interval.unwrap_or(0)){
                queue_ctrl.next_time = value_op1.time.saturating_add(1);
                if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound) {
                    verdict.time = value_op1.time.saturating_add(queue_ctrl.temporal_block.lower_bound);
                    verdict.truth = true;
                    if verdict.time > queue_ctrl.temporal_block.previous.time ||
                    (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                        debug_print!("Right Op true from [i-ub, i-lb]");
                        queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                        return Some(verdict);
                    }
                }
            }
            if ready_op0 && value_op0.truth {
                queue_ctrl.next_time = value_op1.time.saturating_add(1);
                if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound){
                    verdict.time = value_op1.time.saturating_add(queue_ctrl.temporal_block.lower_bound);
                    verdict.truth = true;

                    if verdict.time > queue_ctrl.temporal_block.previous.time ||
                    (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
                        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                        debug_print!("Both True");
                        queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                        return Some(verdict);
                    }
                }
            }
        }
    }
    let start_interval = queue_ctrl.temporal_block.previous.time.checked_sub(queue_ctrl.temporal_block.upper_bound);
    if ready_op0 && !value_op0.truth && value_op0.time >= queue_ctrl.temporal_block.previous.time.saturating_sub(queue_ctrl.temporal_block.lower_bound) &&
        ((queue_ctrl.temporal_block.edge.truth) && (start_interval.is_none() || queue_ctrl.temporal_block.edge.time > start_interval.unwrap_or(0))){
        verdict.time = min(value_op0.time.saturating_add(queue_ctrl.temporal_block.lower_bound), queue_ctrl.temporal_block.edge.time.saturating_add(queue_ctrl.temporal_block.upper_bound));
        verdict.truth = false;

        if verdict.time > queue_ctrl.temporal_block.previous.time ||
        (verdict.time == 0 && !queue_ctrl.temporal_block.previous.truth) {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Left Op False Since Right Op False");
            queue_ctrl.next_time = max(queue_ctrl.next_time, verdict.time.saturating_sub(queue_ctrl.temporal_block.upper_bound).saturating_add(1));
            queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
            return Some(verdict);
        }
    }
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn not_operator(ready_op: r2u2_bool, value_op: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    ensures
        result.is_some() ==> (result.unwrap().truth == !value_op.truth && (queue_ctrl.next_time == value_op.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        !ready_op ==> result.is_none(),
{
    if ready_op {
        queue_ctrl.next_time = value_op.time.saturating_add(1);
        return Some(r2u2_verdict{time: value_op.time, truth: !value_op.truth});
    } else {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Waiting");   
        return None;
    }
}

#[inline(always)]
fn and_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    ensures
        // queue_ctrl.next time doesn't change when neither side is ready or when we cannot evaluate early based on the one side alone
        (!ready_op0 && !ready_op1) || (!ready_op0 && ready_op1 && result.is_none() || (ready_op0 && !ready_op1 && result.is_none())) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

        // lhs and rhs true
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time < value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // lhs and rhs false
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time < value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // lhs false, rhs unknown
        (ready_op0 && !value_op0.truth && !ready_op1) ==> (!result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        // rhs false, lhs unknown
        (!ready_op0 && ready_op1 && !value_op1.truth) ==> (!result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
            
        // not enough information to produce result
        (!ready_op0 && !ready_op1) ==> result.is_none(),
        (ready_op0 && value_op0.truth && !ready_op1) ==> result.is_none(),
        (!ready_op0 && ready_op1 && value_op1.truth) ==> result.is_none(),
{
    let mut verdict = r2u2_verdict::default();
    if ready_op0 && ready_op1 {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Left and Right Ready!");
        if value_op0.truth && value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Both True");
            verdict.time = min(value_op0.time, value_op1.time);
            verdict.truth = true;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        } else if !value_op0.truth && !value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Both False");
            verdict.time = max(value_op0.time, value_op1.time);
            verdict.truth = false;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        }
    }
    if ready_op0 && !value_op0.truth {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Left False");
        verdict.time = value_op0.time;
        verdict.truth = false;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    else if ready_op1 && !value_op1.truth {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Right False");
        verdict.time = value_op1.time;
        verdict.truth = false;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn or_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    ensures
        // queue_ctrl.next time doesn't change when neither side is ready or when we cannot evaluate early based on the one side alone
        (!ready_op0 && !ready_op1) || (!ready_op0 && ready_op1 && result.is_none() || (ready_op0 && !ready_op1 && result.is_none())) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

        // lhs and rhs true
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time < value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // lhs and rhs false
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time < value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // lhs true, rhs unknown
        (ready_op0 && value_op0.truth && !ready_op1) ==> (result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        // rhs true, lhs unknown
        (!ready_op0 && ready_op1 && value_op1.truth) ==> (result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        
        // not enough information to produce result
        (!ready_op0 && !ready_op1) ==> result.is_none(),
        (ready_op0 && !value_op0.truth && !ready_op1) ==> result.is_none(),
        (!ready_op0 && ready_op1 && !value_op1.truth) ==> result.is_none(),
{
    let mut verdict = r2u2_verdict::default();
    if ready_op0 && ready_op1 {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Left and Right Ready!");
        if value_op0.truth && value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Both True");
            verdict.time = max(value_op0.time, value_op1.time);
            verdict.truth = true;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        } else if !value_op0.truth && !value_op1.truth {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Both False");
            verdict.time = min(value_op0.time, value_op1.time);
            verdict.truth = false;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        }
    }
    if ready_op0 && value_op0.truth {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Left True");
        verdict.time = value_op0.time;
        verdict.truth = true;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    else if ready_op1 && value_op1.truth {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Right True");
        verdict.time = value_op1.time;
        verdict.truth = true;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn equivalent_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    ensures
        // queue_ctrl.next time doesn't change unless both sides are ready
        ((!ready_op0 && !ready_op1) || (ready_op0 && !ready_op1) || (!ready_op0 && ready_op1)) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

        // lhs and rhs true
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time < value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // lhs and rhs false
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time < value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // lhs true and rhs false
        (ready_op0 && value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time < value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && value_op0.truth && ready_op1 && !value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),

        // lhs false and rhs true
        (ready_op0 && !value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time < value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op0.time && (queue_ctrl.next_time == value_op0.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        (ready_op0 && !value_op0.truth && ready_op1 && value_op1.truth &&
            value_op0.time >= value_op1.time) ==> (!result.unwrap().truth && result.unwrap().time == value_op1.time && (queue_ctrl.next_time == value_op1.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        
        // not enough information to produce result
        (!ready_op0 && !ready_op1) ==> result.is_none(),
        (ready_op0 && !value_op0.truth && !ready_op1) ==> result.is_none(),
        (!ready_op0 && ready_op1 && !value_op1.truth) ==> result.is_none(),
{
    let mut verdict = r2u2_verdict::default();
    if ready_op0 && ready_op1 {
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        debug_print!("Left and Right Ready!");
        verdict.time = min(value_op0.time, value_op1.time);
        if (value_op0.truth && value_op1.truth) || (!value_op0.truth && !value_op1.truth){
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("Both {}", if value_op1.truth {"True"} else {"False"});
            verdict.truth = true;
        }
        else {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("{} not equivalant to {}", if value_op0.truth {"True"} else {"False"}, if value_op1.truth {"True"} else {"False"});
            verdict.truth = false;
        }
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("Waiting");
    return None;
}

}