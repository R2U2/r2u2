use byteorder::{LittleEndian, ByteOrder};

use crate::memory::{scq::SCQCtrlBlock, monitor::Monitor};
use crate::internals::debug;
    
// MLTL Instruction Opcodes
pub const MLTL_OP_FT_NOP: u8 = 0b11111;
// pub const MLTL_OP_FT_CONFIGURE: u8 = 0b11110;
pub const MLTL_OP_FT_LOAD: u8 = 0b11101;
pub const MLTL_OP_FT_RETURN: u8 = 0b11100;

pub const MLTL_OP_FT_EVENTUALLY: u8 = 0b11011;
pub const MLTL_OP_FT_GLOBALLY: u8 = 0b11010;
pub const MLTL_OP_FT_UNTIL: u8 = 0b11001;
pub const MLTL_OP_FT_RELEASE: u8 = 0b11000;

pub const MLTL_OP_FT_NOT: u8 = 0b10111;
pub const MLTL_OP_FT_AND: u8 = 0b10110;
pub const MLTL_OP_FT_OR: u8 = 0b10101;
pub const MLTL_OP_FT_IMPLIES: u8 = 0b10100;

pub const MLTL_OP_FT_PROB: u8 = 0b10011;
pub const MLTL_OP_FT_XOR: u8 = 0b10001;
pub const MLTL_OP_FT_EQUIVALENT: u8 = 0b10000;

// pub const MLTL_OP_PT_NOP: u8 = 0b01111;
// pub const MLTL_OP_PT_CONFIGURE: u8 = 0b01110;
// pub const MLTL_OP_PT_LOAD: u8 = 0b01101;
// pub const MLTL_OP_PT_RETURN: u8 = 0b01100;

// pub const MLTL_OP_PT_ONCE: u8 = 0b01011;
// pub const MLTL_OP_PT_HISTORICALLY: u8 = 0b01010;
pub const MLTL_OP_PT_SINCE: u8 = 0b01001;
// pub const MLTL_OP_PT_LOCK: u8 = 0b01000;

// pub const MLTL_OP_PT_NOT: u8 = 0b00111;
// pub const MLTL_OP_PT_AND: u8 = 0b00110;
// pub const MLTL_OP_PT_OR: u8 = 0b00101;
// pub const MLTL_OP_PT_IMPLIES: u8 = 0b00100;

// pub const MLTL_OP_PT_NAND: u8 = 0b00011;
// pub const MLTL_OP_PT_NOR: u8 = 0b00010;
// pub const MLTL_OP_PT_XOR: u8 = 0b00001;
// pub const MLTL_OP_PT_EQUIVALENT: u8 = 0b00000;


// MLTL Operand Types
pub const MLTL_OP_TYPE_ATOMIC: u8 = 0b00;
pub const MLTL_OP_TYPE_DIRECT: u8 = 0b01;
pub const MLTL_OP_TYPE_SUBFORMULA: u8 = 0b10;
pub const MLTL_OP_TYPE_NOT_SET: u8 = 0b11;

pub struct MLTLInstruction {
    pub op1_value: u32,
    pub op2_value: u32,
    pub memory_reference: u32,
    pub op1_type: u8,
    pub op2_type: u8,
    pub opcode: u8,
}

impl Copy for MLTLInstruction{ }

impl Clone for MLTLInstruction{
    fn clone(&self) -> MLTLInstruction {
        return *self
    }
}

impl MLTLInstruction {
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
            opcode: MLTL_OP_FT_NOP,
        };
    }
}

pub fn mltl_configure_instruction_dispatch(instr: MLTLInstruction, monitor: &mut Monitor){
    match instr.op1_type{
        MLTL_OP_TYPE_ATOMIC => {
            let mut queue_ref: usize = 0;
            if instr.memory_reference > 0 {
                let prev_queue = monitor.queue_arena.control_blocks[(instr.memory_reference as usize) - 1];
                queue_ref = prev_queue.queue_ref + (prev_queue.length as usize);
            }
            let queue: &mut SCQCtrlBlock = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
            queue.length = instr.op1_value;
            queue.queue_ref = queue_ref;
            debug::print_mltl_config_instruction(instr, *queue);
        },
        MLTL_OP_TYPE_SUBFORMULA => {
            let queue: &mut SCQCtrlBlock = &mut monitor.queue_arena.control_blocks[instr.memory_reference as usize];
            queue.temporal_block.lower_bound = instr.op1_value;
            queue.temporal_block.upper_bound = instr.op2_value;
            queue.length = queue.length - 4; // Required to substract 4 to use same spec file as C version with DUOQs
            debug::print_mltl_config_instruction(instr, *queue);
        },
        _ => {
            // Error
        },
    }
}