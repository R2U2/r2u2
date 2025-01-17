#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
use crate::instructions::{mltl::*, booleanizer::*};
#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
use crate::memory::scq::*;

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

#[cfg(feature = "debug_print_semihosting")]
macro_rules! debug_print {
    ($($args: tt)*) => {
        hprintln!($($args)*);
    }
}

#[cfg(feature = "debug_print_std")]
macro_rules! debug_print {
    ($($args: tt)*) => {
            println!($($args)*);
    }
}

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
pub(crate) use debug_print;

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
pub fn print_mltl_instruction(_instr: MLTLInstruction){
    debug_print!("{:#08x} {:#08x} {:#08x} {:#02x} {:#02x} {:#02x}", _instr.op1_value, _instr.op2_value, _instr.memory_reference, _instr.op1_type, _instr.op2_type, _instr.opcode);
}

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
pub fn print_bz_instruction(_instr: BooleanizerInstruction){
    debug_print!("{:#08x} {:#08x} {:#08x} {:#02x}", _instr.param1, _instr.param2, _instr.memory_reference, _instr.opcode);
}

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
pub fn print_mltl_config_instruction(instr: MLTLInstruction, _ctrl: SCQCtrlBlock){
    debug_print!("{:#08x} {:#08x} {:#08x} {:#02x} {:#02x} {:#02x}", instr.op1_value, instr.op2_value, instr.memory_reference, instr.op1_type, instr.op2_type, instr.opcode);
    match instr.op1_type{
        MLTL_OP_TYPE_ATOMIC => {
            debug_print!("Queue {} -> Length: {}; Memory ref: {}", instr.memory_reference, _ctrl.length, _ctrl.queue_ref);
        },
        MLTL_OP_TYPE_SUBFORMULA => {
            debug_print!("Queue {} -> LB: {}; UB: {}", instr.memory_reference, _ctrl.temporal_block.lower_bound, _ctrl.temporal_block.upper_bound);
        },
        _ => {
            debug_print!("ERROR --- Invalid Config Command!");
        },
    }
}

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
pub fn print_scq(arena: &SCQMemoryArena, queue_id: u32){
    let queue_ctrl = arena.control_blocks[queue_id as usize];
    debug_print!("-------- Queue {} --------", queue_id);
    for n in queue_ctrl.queue_ref..(queue_ctrl.queue_ref+queue_ctrl.length){
        debug_print!("|\t{} -> {}\t|", arena.queue_mem[n as usize].time, arena.queue_mem[n as usize].truth);
    }
    debug_print!("-------------------------");
}