use byteorder::{LittleEndian, ByteOrder};

use crate::memory::{scq::SCQCtrlBlock, monitor::Monitor};
#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
use crate::internals::debug;
    
// MLTL Instruction Opcodes
pub const MLTL_OP_NOP: u8 = 0b11111;

pub const MLTL_OP_LOAD: u8 = 0b11101;
pub const MLTL_OP_RETURN: u8 = 0b11100;

pub const MLTL_OP_EVENTUALLY: u8 = 0b11011;
pub const MLTL_OP_GLOBALLY: u8 = 0b11010;
pub const MLTL_OP_UNTIL: u8 = 0b11001;
pub const MLTL_OP_RELEASE: u8 = 0b11000;

pub const MLTL_OP_NOT: u8 = 0b10111;
pub const MLTL_OP_AND: u8 = 0b10110;
pub const MLTL_OP_OR: u8 = 0b10101;
pub const MLTL_OP_IMPLIES: u8 = 0b10100;

pub const MLTL_OP_PROB: u8 = 0b10011;
pub const MLTL_OP_XOR: u8 = 0b10001;
pub const MLTL_OP_EQUIVALENT: u8 = 0b10000;

pub const MLTL_OP_ONCE: u8 = 0b01011;
pub const MLTL_OP_HISTORICALLY: u8 = 0b01010;
pub const MLTL_OP_SINCE: u8 = 0b01001;
pub const MLTL_OP_TRIGGER: u8 = 0b01000;

// MLTL Operand Types
pub const MLTL_OP_TYPE_ATOMIC: u8 = 0b00;
pub const MLTL_OP_TYPE_DIRECT: u8 = 0b01;
pub const MLTL_OP_TYPE_SUBFORMULA: u8 = 0b10;
pub const MLTL_OP_TYPE_NOT_SET: u8 = 0b11;

#[derive(Copy, Clone)]
pub struct MLTLInstruction {
    pub op1_value: u32,
    pub op2_value: u32,
    pub memory_reference: u32,
    pub op1_type: u8,
    pub op2_type: u8,
    pub opcode: u8,
}

impl MLTLInstruction { // C2PO format sensitive
    pub fn set_from_binary(instr: &[u8]) -> MLTLInstruction{
        return MLTLInstruction{ 
            op1_value: LittleEndian::read_u32(&instr[0..]),
            op2_value: LittleEndian::read_u32(&instr[4..]),
            memory_reference: LittleEndian::read_u32(&instr[8..]),
            op1_type: instr[12],
            op2_type: instr[13],
            opcode: instr[14],
        };
    }
    pub fn empty_instr() -> MLTLInstruction{
        return MLTLInstruction{ 
            op1_value: 0,
            op2_value: 0,
            memory_reference: 0,
            op1_type: MLTL_OP_TYPE_NOT_SET,
            op2_type: MLTL_OP_TYPE_NOT_SET,
            opcode: MLTL_OP_NOP,
        };
    }
}

pub fn mltl_configure_instruction_dispatch(instr: MLTLInstruction, monitor: &mut Monitor){
    match instr.op1_type{
        MLTL_OP_TYPE_ATOMIC => {
            let mut queue_ref: u32 = 0;
            if instr.memory_reference > 0 {
                let prev_queue = monitor.queue_arena.control_blocks[(instr.memory_reference as usize) - 1];
                queue_ref = prev_queue.queue_ref + prev_queue.length;
            }
            let queue: &mut SCQCtrlBlock = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
            queue.length = instr.op1_value;
            queue.queue_ref = queue_ref;
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug::print_mltl_config_instruction(instr, *queue);
        },
        MLTL_OP_TYPE_SUBFORMULA => {
            let queue: &mut SCQCtrlBlock = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
            queue.temporal_block.lower_bound = instr.op1_value;
            queue.temporal_block.upper_bound = instr.op2_value;
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug::print_mltl_config_instruction(instr, *queue);
        },
        _ => {
            // Error
        },
    }
}