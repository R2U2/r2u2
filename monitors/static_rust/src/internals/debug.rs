use byteorder::{LittleEndian, ByteOrder};

use super::super::instructions::{mltl::*, booleanizer::*};
use super::super::memory::scq::*;

#[cfg(embedded)]
use cortex_m_semihosting::hprintln;

#[cfg(not(embedded))]
macro_rules! log {
    ($($args: tt)*) => {
        println!($($args)*);
    }
}

#[cfg(all(not(embedded),feature = "debug_print"))]
macro_rules! debug_print {
    ($($args: tt)*) => {
            println!($($args)*);
    }
}

#[cfg(embedded)]
macro_rules! log {
    ($($args: tt)*) => {
        hprintln!($($args)*);
    }
}

#[cfg(all(embedded,feature = "debug_print"))]
macro_rules! debug_print {
    ($($args: tt)*) => {
        hprintln!($($args)*);
    }
}

#[cfg(not(feature = "debug_print"))]
macro_rules! debug_print {
    ($($args: tt)*) => {
    }
}

pub(crate) use log;
pub(crate) use debug_print;

pub fn print_mltl_instruction(instr: MLTLInstruction){
    debug_print!("{:#08x} {:#08x} {:#08x} {:#02x} {:#02x} {:#02x}", instr.op1_value, instr.op2_value, instr.memory_reference, instr.op1_type, instr.op2_type, instr.opcode);
}

pub fn print_bz_instruction(instr: BooleanizerInstruction){
    debug_print!("{:#016x} {:#08x} {:#08x} {:#08x} {:#02x} {:#02x}", LittleEndian::read_u64(&instr.param1), instr.param2, instr.memory_reference, instr.at_addr, instr.store as u8, instr.opcode);
}

pub fn print_mltl_config_instruction(instr: MLTLInstruction, ctrl: SCQCtrlBlock){
    debug_print!("{:#08x} {:#08x} {:#08x} {:#02x} {:#02x} {:#02x}", instr.op1_value, instr.op2_value, instr.memory_reference, instr.op1_type, instr.op2_type, instr.opcode);
    match instr.op1_type{
        MLTL_OP_TYPE_ATOMIC => {
            debug_print!("Queue {} -> Length: {}; Memory ref: {}", instr.memory_reference, ctrl.length, ctrl.queue_ref);
        },
        MLTL_OP_TYPE_SUBFORMULA => {
            debug_print!("Queue {} -> LB: {}; UB: {}", instr.memory_reference, ctrl.temporal_block.lower_bound, ctrl.temporal_block.upper_bound);
        },
        _ => {
            debug_print!("ERROR --- Invalid Config Command!");
        },
    }
}

pub fn print_scq(arena: &SCQMemoryArena, queue_id: u32){
    let queue_ctrl = arena.control_blocks[queue_id as usize];
    debug_print!("-------- Queue {} --------", queue_id);
    for n in queue_ctrl.queue_ref..(queue_ctrl.queue_ref+queue_ctrl.length as usize){
        debug_print!("|\t{} -> {}\t|", arena.queue_mem[n].time, arena.queue_mem[n].truth);
    }
    debug_print!("-------------------------");
}