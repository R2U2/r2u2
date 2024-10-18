use byteorder::{LittleEndian, ByteOrder};
use libm::{pow, sqrt};

use crate::engines::r2u2_float;
use crate::internals::bounds::R2U2_FLOAT_EPSILON;

use super::super::instructions::booleanizer::*;
use super::super::memory::monitor::*;
use super::super::internals::debug::*;


fn float_to_bool(f: r2u2_float) -> bool{
    if f == 0.0 {
        return false;
    } else{
        return true;
    }
}

pub fn bz_update(monitor: &mut Monitor){
    let instr = monitor.bz_instruction_table[monitor.bz_program_count.curr_program_count];
    match instr.opcode{
        BZ_OP_NONE => {
            return;
        }
        BZ_OP_ILOAD => {
            debug_print!("BZ ILOAD");
            let signal_reference = LittleEndian::read_u32(&instr.param1);
            monitor.value_buffer[instr.memory_reference as usize] = monitor.signal_buffer[signal_reference as usize];
            debug_print!("b{} = {} (s{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize] as i32, signal_reference);
        }
        BZ_OP_FLOAD => {
            debug_print!("BZ FLOAD");
            let signal_reference = LittleEndian::read_u32(&instr.param1);
            monitor.value_buffer[instr.memory_reference as usize] = monitor.signal_buffer[signal_reference as usize];
            debug_print!("b{} = {} (s{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize] as r2u2_float, signal_reference);  
        }
        BZ_OP_ICONST=> {
            debug_print!("BZ ICONST");
            let op_const = LittleEndian::read_i32(&instr.param1);
            monitor.value_buffer[instr.memory_reference as usize] = op_const as r2u2_float;
            debug_print!("b{} = {}", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize] as i32);
        }
        BZ_OP_FCONST=> {
            debug_print!("BZ FCONST");
            let op_const = LittleEndian::read_f64(&instr.param1);
            monitor.value_buffer[instr.memory_reference as usize] = op_const as r2u2_float;
            debug_print!("b{} = {}", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize] as r2u2_float);
        BZ_OP_STORE => {
            debug_print!("BZ STORE");
            let op = float_to_bool(monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize]);
            monitor.atomic_buffer[instr.param2 as usize] = op;
            debug_print!("a{} = {} (b{})", instr.param2, monitor.atomic_buffer[instr.param2 as usize], LittleEndian::read_u32(&instr.param1) as usize);
        }
        BZ_OP_BWNEG=> {
            debug_print!("BZ BWNEG");
            let op = float_to_bool(monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize]);
            monitor.value_buffer[instr.memory_reference as usize] = !op as i32 as r2u2_float;
            debug_print!("b{} = {} = (~{})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op);
        }
        BZ_OP_BWAND=> {
            debug_print!("BZ BWAND");
            let op0 = float_to_bool(monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize]);
            let op1 = float_to_bool(monitor.value_buffer[instr.param2 as usize]);
            monitor.value_buffer[instr.memory_reference as usize] = (op0 & op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} & {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_BWOR=> {
            debug_print!("BZ BWOR");
            let op0 = float_to_bool(monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize]);
            let op1 = float_to_bool(monitor.value_buffer[instr.param2 as usize]);
            monitor.value_buffer[instr.memory_reference as usize] = (op0 | op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} | {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_BWXOR=> {
            debug_print!("BZ BWXOR");
            let op0 = float_to_bool(monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize]);
            let op1 = float_to_bool(monitor.value_buffer[instr.param2 as usize]);
            monitor.value_buffer[instr.memory_reference as usize] = (op0 ^ op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} ^ {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_IEQ=> {
            debug_print!("BZ IEQ");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 == op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_FEQ=> {
            debug_print!("BZ FEQ");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = (if op0 > op1 {op0-op1 < R2U2_FLOAT_EPSILON} else {op1-op0 < R2U2_FLOAT_EPSILON}) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_INEQ=> {
            debug_print!("BZ INEQ");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 != op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_FNEQ=> {
            debug_print!("BZ FNEQ");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = !(if op0 > op1 {op0-op1 < R2U2_FLOAT_EPSILON} else {op1-op0 < R2U2_FLOAT_EPSILON}) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_IGT=> {
            debug_print!("BZ IGT");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 > op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} > {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_FGT=> {
            debug_print!("BZ FGT");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = (op0 > op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} > {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_IGTE=> {            
            debug_print!("BZ IGTE");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 >= op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} >= {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_FGTE=> {
            debug_print!("BZ FGTE");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = (op0 > (op1 - R2U2_FLOAT_EPSILON)) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} >= {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_ILT=> {
            debug_print!("BZ ILT");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 < op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} < {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_FLT=> {
            debug_print!("BZ FLT");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = (op0 < op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} < {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_ILTE=> {
            debug_print!("BZ ILTE");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 <= op1) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} <= {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_FLTE=> {
            debug_print!("BZ FLTE");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = (op0 < (op1 + R2U2_FLOAT_EPSILON)) as i32 as r2u2_float;
            debug_print!("b{} = {} = ({} <= {})", instr.memory_reference, float_to_bool(monitor.value_buffer[instr.memory_reference as usize]), op0, op1);
        }
        BZ_OP_INEG | BZ_OP_FNEG => {
            debug_print!("BZ NEG");
            let op = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            monitor.value_buffer[instr.memory_reference as usize] = -1.0 * op;
            debug_print!("b{} = {} = (-1 * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op);
        }
        BZ_OP_IADD | BZ_OP_FADD => {
            debug_print!("BZ ADD");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op0 + op1;
            debug_print!("b{} = {} = ({} + {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op0, op1);
        }
        BZ_OP_ISUB | BZ_OP_FSUB=> {
            debug_print!("BZ SUB");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op0 - op1;
            debug_print!("b{} = {} = ({} - {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op0, op1);
        }
        BZ_OP_IMUL | BZ_OP_FMUL => {
            debug_print!("BZ MUL");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op0 * op1;
            debug_print!("b{} = {} = ({} * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op0, op1);
        }
        BZ_OP_IDIV=> {
            debug_print!("BZ IDIV");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 / op1) as r2u2_float;
            debug_print!("b{} = {} = ({} / {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize] as i32, op0, op1);
        }
        BZ_OP_FDIV=> {
            debug_print!("BZ FDIV");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op0 / op1;
            debug_print!("b{} = {} = ({} / {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op0, op1);
        }
        BZ_OP_MOD=> {
            debug_print!("BZ MOD");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as i32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0 % op1) as r2u2_float;
            debug_print!("b{} = {} = ({} % {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op0, op1);
        }
        BZ_OP_IPOW=> {
            debug_print!("BZ IPOW");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize] as i32;
            let op1 = monitor.value_buffer[instr.param2 as usize] as u32;
            monitor.value_buffer[instr.memory_reference as usize] = (op0.pow(op1)) as r2u2_float;
            debug_print!("b{} = {} = ({} pow {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize] as i32, op0, op1);
        }
        BZ_OP_FPOW=> {
            debug_print!("BZ FPOW");
            let op0 = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            let op1 = monitor.value_buffer[instr.param2 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = pow(op0, op1);
            debug_print!("b{} = {} = ({} pow {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op0, op1);
        }
        BZ_OP_ISQRT=> {
            debug_print!("BZ ISQRT");
            let op = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            // monitor.value_buffer[instr.memory_reference as usize] = op.checked_isqrt().unwrap_or(0) as r2u2_float;
            monitor.value_buffer[instr.memory_reference as usize] = sqrt(op) as i32 as r2u2_float;
            debug_print!("b{} = {} = (sqrt {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize] as i32, op);
        }
        BZ_OP_FSQRT=> {
            debug_print!("BZ FSQRT");
            let op = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            monitor.value_buffer[instr.memory_reference as usize] = sqrt(op);
            debug_print!("b{} = {} = (sqrt {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op);
        }
        BZ_OP_IABS | BZ_OP_FABS=> {
            debug_print!("BZ ABS");
            let op = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op.abs();
            debug_print!("b{} = {} = (|{}|)", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize], op);
        }
        BZ_OP_IPREV | BZ_OP_FPREV => {
            debug_print!("BZ PREV");
            let op = monitor.value_buffer[LittleEndian::read_u32(&instr.param1) as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op;
            debug_print!("b{} = {}", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize]);
        }
        _ => {
            return;
        }
    }
}