use libm::{pow, sqrt};

use crate::internals::bounds::R2U2_FLOAT_EPSILON;

use super::super::instructions::booleanizer::*;
use super::super::memory::monitor::*;
use super::super::internals::{debug::*, types::*};

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

pub fn bz_update(monitor: &mut Monitor){
    let instr = monitor.bz_instruction_table[monitor.bz_program_count.curr_program_count];
    match instr.opcode{
        BZ_OP_NONE => {
            return;
        }
        BZ_OP_ILOAD => {
            debug_print!("BZ ILOAD");
            monitor.value_buffer[instr.memory_reference as usize].i = monitor.signal_buffer[instr.param1 as usize].i;
            debug_print!("b{} = {} (s{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, instr.param1);  
        }
        BZ_OP_FLOAD => {
            debug_print!("BZ FLOAD");
            monitor.value_buffer[instr.memory_reference as usize].f = monitor.signal_buffer[instr.param1 as usize].f;
            debug_print!("b{} = {} (s{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, instr.param1);  
        }
        BZ_OP_STORE => {
            debug_print!("BZ STORE");
            let op = monitor.value_buffer[instr.param1 as usize].i;
            monitor.atomic_buffer[instr.param2 as usize] = if op == 0 {false} else {true};
            debug_print!("a{} = {} (b{})", instr.param2, monitor.atomic_buffer[instr.param2 as usize], instr.param1 as usize);
        }
        BZ_OP_BWNEG=> {
            debug_print!("BZ BWNEG");
            monitor.value_buffer[instr.memory_reference as usize].i = !op;
            let op = monitor.value_buffer[instr.param1 as usize].i;
            debug_print!("b{} = {} = (~{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_BWAND=> {
            debug_print!("BZ BWAND");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 & op1;
            debug_print!("b{} = {} = ({} & {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_BWOR=> {
            debug_print!("BZ BWOR");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 | op1;
            debug_print!("b{} = {} = ({} | {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_BWXOR=> {
            debug_print!("BZ BWXOR");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 ^ op1;
            debug_print!("b{} = {} = ({} ^ {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IEQ=> {
            debug_print!("BZ IEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 == op1) as r2u2_int;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FEQ=> {
            debug_print!("BZ FEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = (if op0 > op1 {op0-op1 < R2U2_FLOAT_EPSILON} else {op1-op0 < R2U2_FLOAT_EPSILON}) as r2u2_int;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_INEQ=> {
            debug_print!("BZ INEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 != op1) as r2u2_int;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FNEQ=> {
            debug_print!("BZ FNEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = !(if op0 > op1 {op0-op1 < R2U2_FLOAT_EPSILON} else {op1-op0 < R2U2_FLOAT_EPSILON}) as r2u2_int;
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IGT=> {
            debug_print!("BZ IGT");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 > op1) as r2u2_int;
            debug_print!("b{} = {} = ({} > {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FGT=> {
            debug_print!("BZ FGT");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 > op1) as r2u2_int;
            debug_print!("b{} = {} = ({} > {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IGTE=> {            
            debug_print!("BZ IGTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 >= op1) as r2u2_int;
            debug_print!("b{} = {} = ({} >= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FGTE=> {
            debug_print!("BZ FGTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 > (op1 - R2U2_FLOAT_EPSILON)) as r2u2_int;
            debug_print!("b{} = {} = ({} >= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_ILT=> {
            debug_print!("BZ ILT");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 < op1) as r2u2_int;
            debug_print!("b{} = {} = ({} < {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FLT=> {
            debug_print!("BZ FLT");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 < op1) as r2u2_int;
            debug_print!("b{} = {} = ({} < {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_ILTE=> {
            debug_print!("BZ ILTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 <= op1) as r2u2_int;
            debug_print!("b{} = {} = ({} <= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FLTE=> {
            debug_print!("BZ FLTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = (op0 < (op1 + R2U2_FLOAT_EPSILON)) as r2u2_int;
            debug_print!("b{} = {} = ({} <= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_INEG =>{
            debug_print!("BZ INEG");
            monitor.value_buffer[instr.memory_reference as usize].i = -1 * op;
            let op = monitor.value_buffer[instr.param1 as usize].i;
            debug_print!("b{} = {} = (-1 * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_FNEG => {
            debug_print!("BZ FNEG");
            monitor.value_buffer[instr.memory_reference as usize].f = -1.0 * op;
            let op = monitor.value_buffer[instr.param1 as usize].f;
            debug_print!("b{} = {} = (-1 * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op);
        }
        BZ_OP_IADD => {
            debug_print!("BZ IADD");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 + op1;
            debug_print!("b{} = {} = ({} + {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FADD => {
            debug_print!("BZ FADD");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = op0 + op1;
            debug_print!("b{} = {} = ({} + {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_ISUB => {
            debug_print!("BZ ISUB");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 - op1;
            debug_print!("b{} = {} = ({} - {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FSUB => {
            debug_print!("BZ FSUB");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = op0 - op1;
            debug_print!("b{} = {} = ({} - {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_IMUL => {
            debug_print!("BZ IMUL");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 * op1;
            debug_print!("b{} = {} = ({} * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FMUL => {
            debug_print!("BZ FMUL");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = op0 * op1;
            debug_print!("b{} = {} = ({} * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_IDIV=> {
            debug_print!("BZ IDIV");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 / op1;
            debug_print!("b{} = {} = ({} / {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FDIV=> {
            debug_print!("BZ FDIV");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = op0 / op1;
            debug_print!("b{} = {} = ({} / {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_MOD=> {
            debug_print!("BZ MOD");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = op0 % op1;
            debug_print!("b{} = {} = ({} % {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IPOW=> {
            debug_print!("BZ IPOW");
            let op1 = monitor.value_buffer[instr.param2 as usize].i as u32;
            monitor.value_buffer[instr.memory_reference as usize].i = op0.pow(op1);
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            debug_print!("b{} = {} = ({} pow {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FPOW=> {
            debug_print!("BZ FPOW");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = pow(op0, op1);
            debug_print!("b{} = {} = ({} pow {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_ISQRT=> {
            debug_print!("BZ ISQRT");
            // monitor.value_buffer[instr.memory_reference as usize] = op.checked_isqrt().unwrap_or(0) as r2u2_float;
            monitor.value_buffer[instr.memory_reference as usize].i = sqrt(op as r2u2_float) as r2u2_int;
            let op = monitor.value_buffer[instr.param1 as usize].i;
            debug_print!("b{} = {} = (sqrt {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_FSQRT=> {
            debug_print!("BZ FSQRT");
            monitor.value_buffer[instr.memory_reference as usize].f = sqrt(op);
            let op = monitor.value_buffer[instr.param1 as usize].f;
            debug_print!("b{} = {} = (sqrt {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op);
        }
        BZ_OP_IABS => {
            debug_print!("BZ IABS");
            monitor.value_buffer[instr.memory_reference as usize].i = op.abs();
            let op = monitor.value_buffer[instr.param1 as usize].i;
            debug_print!("b{} = {} = (|{}|)", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_FABS => {
            debug_print!("BZ FABS");
            monitor.value_buffer[instr.memory_reference as usize].f = if op < 0.0 {-op} else {op};
            let op = monitor.value_buffer[instr.param1 as usize].f;
            debug_print!("b{} = {} = (|{}|)", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op);
        }
        BZ_OP_PREV => {
            debug_print!("BZ PREV");
            let op = monitor.value_buffer[instr.param1 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op;
            debug_print!("b{} = {}/{}", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, monitor.value_buffer[instr.memory_reference as usize].f);
        }
        _ => {
            return;
        }
    }
}