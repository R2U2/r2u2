use crate::instructions::mltl::*;
use crate::internals::{debug::*, types::*};
use crate::memory::{monitor::*,scq::*};

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
            // Only directly load in T or F on first loop of time step
            if monitor.progress == MonitorProgressState::FirstLoop {
                return Some(r2u2_verdict{time: monitor.time_stamp, truth: value != 0});
            }
        }
        MLTL_OP_TYPE_SUBFORMULA => {
            // Handled by the SCQ check function, just need to pass it the appropriate arguments
            let op_id = if op_num == 0 {instr.op1_value} else {instr.op2_value};
            return scq_read(monitor, instr.memory_reference, op_id, op_num);
        }
        MLTL_OP_TYPE_NOT_SET => {
            // Error
            return None;
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
    let queue_ctrl = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
    
    queue_ctrl.next_time = verdict.time + 1;
    debug_print!("Desired time {}", queue_ctrl.next_time);

    simple_push_result(instr, monitor, verdict);
}

#[verifier::external]
fn simple_push_result(instr: MLTLInstruction, monitor: &mut Monitor, verdict: r2u2_verdict){
    
    if monitor.progress == MonitorProgressState::ReloopNoProgress {
        monitor.progress = MonitorProgressState::ReloopWithProgress;
    }

    scq_write(monitor, instr.memory_reference, verdict);
}

#[verifier::external]
pub fn mltl_ft_update(monitor: &mut Monitor){
    let instr = monitor.mltl_instruction_table[monitor.mltl_program_count.curr_program_count];
    match instr.opcode {
        MLTL_OP_FT_NOP => {
            return;
        }
        MLTL_OP_FT_LOAD => {
            debug_print!("FT LOAD");
            let verdict = check_operand_data(instr, monitor, 0);
            if verdict.is_some() {
                push_result(instr, monitor, verdict.unwrap());
            }
        }
        MLTL_OP_FT_RETURN => {
            debug_print!("FT RETURN");
            let verdict = check_operand_data(instr, monitor, 0);
            if verdict.is_some() {
                push_result(instr, monitor, verdict.unwrap());
                debug_print!("{}:{},{}", instr.op2_value, verdict.unwrap().time, if verdict.unwrap().truth {"T"} else {"F"});
                monitor.output_buffer[monitor.output_buffer_idx] = r2u2_output{spec_num: instr.op2_value, verdict: verdict.unwrap()};
                monitor.output_buffer_idx += 1;
            }
        }
        MLTL_OP_FT_EVENTUALLY => {
            return;
        }
        MLTL_OP_FT_GLOBALLY => {
            debug_print!("FT GLOBAL");
            let op = check_operand_data(instr, monitor, 0);
            if op.is_some() {
                let op = op.unwrap();
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
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            match until_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]){
                Some(result) => simple_push_result(instr, monitor, result),
                None => (),
            }
        }
        MLTL_OP_FT_RELEASE => {
            return;
        }
        MLTL_OP_FT_NOT => {
            debug_print!("FT NOT");
            let op = check_operand_data(instr, monitor, 0);
            match not_operator(op.is_some(), op.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]){
                Some(result) => simple_push_result(instr, monitor, result),
                None => (),
            }
        }
        MLTL_OP_FT_AND => {
            debug_print!("FT AND");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            match and_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]){
                Some(result) => simple_push_result(instr, monitor, result),
                None => (),
            }
        }
        MLTL_OP_FT_OR => {
            debug_print!("FT OR");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            match or_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]){
                Some(result) => simple_push_result(instr, monitor, result),
                None => (),
            }
        }
        MLTL_OP_FT_IMPLIES => {
            return;
        }
        MLTL_OP_FT_PROB => {
            return;
        }
        MLTL_OP_FT_XOR => {
            return;
        }
        MLTL_OP_FT_EQUIVALENT => {
            debug_print!("FT EQUIVALENT");
            let op0 = check_operand_data(instr, monitor, 0);
            let op1 = check_operand_data(instr, monitor, 1);
            match equivalent_operator(op0.is_some(), op0.unwrap_or_default(), op1.is_some(), op1.unwrap_or_default(), &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize]){
                Some(result) => simple_push_result(instr, monitor, result),
                None => (),
            }
        }
        _ => {
            return;
        }
    }
}

#[allow(dead_code)]
#[verifier(external_fn_specification)] // Verus doesn't support saturating_sub; therefore, have to provide specification for it
pub fn ex_saturating_sub(lhs: r2u2_time, rhs: r2u2_time) -> (result: r2u2_time)
    ensures
        result == lhs - rhs || result == r2u2_time::MAX || result == r2u2_time::MIN,
        (lhs - rhs > r2u2_time::MAX) ==> result == r2u2_time::MAX,
        (lhs - rhs < r2u2_time::MIN) ==> result == r2u2_time::MIN,
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
        !result.is_some() ==> queue_ctrl.temporal_block.previous.time == old(queue_ctrl).temporal_block.previous.time,
        
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
        (!ready_op0 && !ready_op1) || (!ready_op0 && ready_op1 && !result.is_some()) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

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
        (ready_op0 && !ready_op1) ==> !result.is_some(),
        (!ready_op0 && !ready_op1) ==> !result.is_some(),
        (value_op0.truth && !value_op1.truth &&
            value_op1.time < old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound && 
                old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound <= r2u2_time::MAX) ==> !result.is_some(),
        (!ready_op0 && !value_op1.truth &&
            value_op1.time < old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound && 
                old(queue_ctrl).temporal_block.previous.time + queue_ctrl.temporal_block.upper_bound <= r2u2_time::MAX) ==> !result.is_some(),
        
{
    let mut verdict = r2u2_verdict::default();
    if ready_op1 {
        // If op1 is true at lb, then true
        if value_op1.truth {
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
                    debug_print!("Left and Right Op False");
                    verdict.time = tau - queue_ctrl.temporal_block.lower_bound;
                    verdict.truth = false;

                    queue_ctrl.temporal_block.previous = r2u2_verdict{time: verdict.time, truth: true};
                    return Some(verdict);
                }
        }
        // if op1 is false the entire interval [lb, ub], then false
        if value_op1.time >= queue_ctrl.temporal_block.previous.time.saturating_add(queue_ctrl.temporal_block.upper_bound){
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
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn not_operator(ready_op: r2u2_bool, value_op: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    ensures
        result.is_some() ==> (result.unwrap().truth == !value_op.truth && (queue_ctrl.next_time == value_op.time + 1 || queue_ctrl.next_time == r2u2_time::MAX)),
        !ready_op ==> !result.is_some(),
{
    if ready_op {
        queue_ctrl.next_time = value_op.time.saturating_add(1);
        return Some(r2u2_verdict{time: value_op.time, truth: !value_op.truth});
    } else {
        debug_print!("Waiting");   
        return None;
    }
}

#[inline(always)]
fn and_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    ensures
        // queue_ctrl.next time doesn't change when neither side is ready or when we cannot evaluate early based on the one side alone
        (!ready_op0 && !ready_op1) || (!ready_op0 && ready_op1 && !result.is_some() || (ready_op0 && !ready_op1 && !result.is_some())) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

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
        (!ready_op0 && !ready_op1) ==> !result.is_some(),
        (ready_op0 && value_op0.truth && !ready_op1) ==> !result.is_some(),
        (!ready_op0 && ready_op1 && value_op1.truth) ==> !result.is_some(),
{
    let mut verdict = r2u2_verdict::default();
    if ready_op0 && ready_op1 {
        debug_print!("Left and Right Ready!");
        if value_op0.truth && value_op1.truth {
            debug_print!("Both True");
            verdict.time = min(value_op0.time, value_op1.time);
            verdict.truth = true;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        } else if !value_op0.truth && !value_op1.truth {
            debug_print!("Both False");
            verdict.time = max(value_op0.time, value_op1.time);
            verdict.truth = false;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        }
    }
    if ready_op0 && !value_op0.truth {
        debug_print!("Left False");
        verdict.time = value_op0.time;
        verdict.truth = false;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    else if ready_op1 && !value_op1.truth {
        debug_print!("Right False");
        verdict.time = value_op1.time;
        verdict.truth = false;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    debug_print!("Waiting");
    return None;
}

#[inline(always)]
fn or_operator(ready_op0: r2u2_bool, value_op0: r2u2_verdict, ready_op1: r2u2_bool, value_op1: r2u2_verdict, queue_ctrl: &mut SCQCtrlBlock) -> (result: Option<r2u2_verdict>) 
    ensures
        // queue_ctrl.next time doesn't change when neither side is ready or when we cannot evaluate early based on the one side alone
        (!ready_op0 && !ready_op1) || (!ready_op0 && ready_op1 && !result.is_some() || (ready_op0 && !ready_op1 && !result.is_some())) ==> queue_ctrl.next_time == old(queue_ctrl).next_time,

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
        (!ready_op0 && !ready_op1) ==> !result.is_some(),
        (ready_op0 && !value_op0.truth && !ready_op1) ==> !result.is_some(),
        (!ready_op0 && ready_op1 && !value_op1.truth) ==> !result.is_some(),
{
    let mut verdict = r2u2_verdict::default();
    if ready_op0 && ready_op1 {
        debug_print!("Left and Right Ready!");
        if value_op0.truth && value_op1.truth {
            debug_print!("Both True");
            verdict.time = max(value_op0.time, value_op1.time);
            verdict.truth = true;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        } else if !value_op0.truth && !value_op1.truth {
            debug_print!("Both False");
            verdict.time = min(value_op0.time, value_op1.time);
            verdict.truth = false;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        }
    }
    if ready_op0 && value_op0.truth {
        debug_print!("Left True");
        verdict.time = value_op0.time;
        verdict.truth = true;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
    else if ready_op1 && value_op1.truth {
        debug_print!("Right True");
        verdict.time = value_op1.time;
        verdict.truth = true;
        queue_ctrl.next_time = verdict.time.saturating_add(1);
        return Some(verdict);
    }
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

        // not enough information to produce result
        (!ready_op0 && !ready_op1) ==> !result.is_some(),
        (ready_op0 && !value_op0.truth && !ready_op1) ==> !result.is_some(),
        (!ready_op0 && ready_op1 && !value_op1.truth) ==> !result.is_some(),
{
    let mut verdict = r2u2_verdict::default();
    if ready_op0 && ready_op1 {
        debug_print!("Left and Right Ready!");
        if (value_op0.truth && value_op1.truth) || !value_op0.truth && !value_op1.truth{
            debug_print!("Both {}", if value_op1.truth {"True"} else {"False"});
            verdict.time = min(value_op0.time, value_op1.time);
            verdict.truth = true;
            queue_ctrl.next_time = verdict.time.saturating_add(1);
            return Some(verdict);
        }
    }
    debug_print!("Waiting");
    return None;
}

}