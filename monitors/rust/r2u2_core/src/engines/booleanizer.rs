use libm::{pow, sqrt};

use crate::internals::bounds::R2U2_FLOAT_EPSILON;

use crate::instructions::booleanizer::*;
use crate::memory::monitor::Monitor;
use crate::internals::types::*;

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
use crate::internals::debug::*;

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

use vstd::prelude::*;

verus! {

#[verifier::external] // Verus doesn't support the feature for writing to the monitor.value_buffer  
pub fn bz_update(monitor: &mut Monitor){
    let instr = monitor.bz_instruction_table[monitor.bz_program_count.curr_program_count];
    match instr.opcode{
        BZ_OP_ILOAD => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ ILOAD");
            monitor.value_buffer[instr.memory_reference as usize].i = monitor.signal_buffer[instr.param1 as usize].i;
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} (s{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, instr.param1);  
        }
        BZ_OP_FLOAD => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FLOAD");
            monitor.value_buffer[instr.memory_reference as usize].f = monitor.signal_buffer[instr.param1 as usize].f;
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} (s{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, instr.param1);  
        }
        BZ_OP_STORE => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ STORE");
            let op = monitor.value_buffer[instr.param1 as usize].i;
            monitor.atomic_buffer[instr.param2 as usize] = op != 0;
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("a{} = {} (b{})", instr.param2, monitor.atomic_buffer[instr.param2 as usize], instr.param1 as usize);
        }
        BZ_OP_BWNEG=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ BWNEG");
            let op = monitor.value_buffer[instr.param1 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = bitwise_negation(op);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = (~{})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_BWAND=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ BWAND");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = bitwise_and(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} & {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_BWOR=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ BWOR");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = bitwise_or(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} | {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_BWXOR=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ BWXOR");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = bitwise_xor(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} ^ {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IEQ=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = integer_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FEQ=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = float_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_INEQ=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ INEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = integer_not_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FNEQ=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FNEQ");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = float_not_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} == {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IGT=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IGT");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = integer_greater_than(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} > {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FGT=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FGT");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = float_greater_than(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} > {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IGTE=> {            
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IGTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = integer_greater_than_or_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} >= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FGTE=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FGTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = float_greater_than_or_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} >= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_ILT=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ ILT");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = integer_less_than(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} < {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FLT=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FLT");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = float_less_than(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} < {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_ILTE=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ ILTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = integer_less_than_or_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} <= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FLTE=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FLTE");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].i = float_less_than_or_equal(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} <= {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_INEG =>{
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ INEG");
            let op = monitor.value_buffer[instr.param1 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_negative(op);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = (-1 * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_FNEG => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FNEG");
            let op = monitor.value_buffer[instr.param1 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_negative(op);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = (-1 * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op);
        }
        BZ_OP_IADD => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IADD");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_add(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} + {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FADD => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FADD");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_add(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} + {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_ISUB => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ ISUB");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_subtract(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} - {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FSUB => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FSUB");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_subtract(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} - {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_IMUL => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IMUL");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_multiply(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FMUL => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FMUL");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_multiply(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} * {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_IDIV=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IDIV");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_divide(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} / {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FDIV=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FDIV");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_divide(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} / {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_MOD=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ MOD");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_mod(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} % {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_IPOW=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IPOW");
            let op0 = monitor.value_buffer[instr.param1 as usize].i;
            let op1 = monitor.value_buffer[instr.param2 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_power(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} pow {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op0, op1);
        }
        BZ_OP_FPOW=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FPOW");
            let op0 = monitor.value_buffer[instr.param1 as usize].f;
            let op1 = monitor.value_buffer[instr.param2 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_power(op0, op1);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = ({} pow {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op0, op1);
        }
        BZ_OP_ISQRT=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ ISQRT");
            let op = monitor.value_buffer[instr.param1 as usize].i;
            monitor.value_buffer[instr.memory_reference as usize].i = integer_square_root(op);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = (sqrt {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_FSQRT=> {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FSQRT");
            let op = monitor.value_buffer[instr.param1 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_square_root(op);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = (sqrt {})", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op);
        }
        BZ_OP_IABS => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ IABS");
            let op = monitor.value_buffer[instr.param1 as usize].i;
            (monitor.value_buffer[instr.memory_reference as usize].i, monitor.overflow_error) = integer_absolute_value(op);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = (|{}|)", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, op);
        }
        BZ_OP_FABS => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ FABS");
            let op = monitor.value_buffer[instr.param1 as usize].f;
            monitor.value_buffer[instr.memory_reference as usize].f = float_absolute_value(op);
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {} = (|{}|)", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f, op);
        }
        BZ_OP_PREV => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ PREV");
            let op = monitor.value_buffer[instr.param1 as usize];
            monitor.value_buffer[instr.memory_reference as usize] = op;
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {}/{}", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i, monitor.value_buffer[instr.memory_reference as usize].f);
        }
        BZ_TS => {
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("BZ TS");
            monitor.value_buffer[instr.memory_reference as usize].i = if monitor.time_stamp > (r2u2_int::MAX as u32) {r2u2_int::MAX} else { monitor.time_stamp as i32 };
            #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
            debug_print!("b{} = {}", instr.memory_reference, monitor.time_stamp);
        }
        _ => {
            return;
        }
    }
}

#[inline(always)]
fn bitwise_negation(op: r2u2_int) -> (result: r2u2_int)
    ensures
        result == (!op),
{
    return !op;
}

#[inline(always)]
fn bitwise_and(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == (op0 & op1),
{
    return op0 & op1;
}

#[inline(always)]
fn bitwise_or(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == (op0 | op1),
{
    return op0 | op1;
}

#[inline(always)]
fn bitwise_xor(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == (op0 ^ op1),
{
    return op0 ^ op1;
}

#[inline(always)]
fn integer_equal(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == 0 || result == 1,
        op0 == op1 ==> result == 1,
        op0 != op1 ==> result == 0,
{
    if op0 == op1 {
        return 1;
    } else {
        return 0;
    }
}

#[verifier::external]  // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_equal(op0: r2u2_float, op1: r2u2_float) -> r2u2_int {
    if float_absolute_value(op0 - op1) <= R2U2_FLOAT_EPSILON {
        return 1;
    } else {
        return 0;
    }
}

#[inline(always)]
fn integer_not_equal(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == 0 || result == 1,
        op0 != op1 ==> result == 1,
        op0 == op1 ==> result == 0,
{
    if op0 != op1 {
        return 1;
    } else {
        return 0;
    }
}

#[verifier::external]  // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_not_equal(op0: r2u2_float, op1: r2u2_float) -> r2u2_int {
    if float_absolute_value(op0 - op1) > R2U2_FLOAT_EPSILON {
        return 1;
    } else {
        return 0;
    }
}

#[inline(always)]
fn integer_greater_than(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == 0 || result == 1,
        op0 > op1 ==> result == 1,
        op0 <= op1 ==> result == 0,
{
    if op0 > op1 {
        return 1;
    } else {
        return 0;
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_greater_than(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_int)
{
    if (op0 > op1) && (float_not_equal(op0, op1) == 1){
        return 1;
    } else {
        return 0;
    }
}

#[inline(always)]
fn integer_greater_than_or_equal(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == 0 || result == 1,
        op0 >= op1 ==> result == 1,
        op0 < op1 ==> result == 0,
{
    if op0 >= op1 {
        return 1;
    } else {
        return 0;
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_greater_than_or_equal(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_int)
{
    if (op0 > op1) || (float_equal(op0, op1) == 1) {
        return 1;
    } else {
        return 0;
    }
}

#[inline(always)]
fn integer_less_than(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == 0 || result == 1,
        op0 < op1 ==> result == 1,
        op0 >= op1 ==> result == 0,
{
    if op0 < op1 {
        return 1;
    } else {
        return 0;
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_less_than(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_int)
{
    if (op0 < op1) && (float_not_equal(op0, op1) == 1){
        return 1;
    } else {
        return 0;
    }
}

#[inline(always)]
fn integer_less_than_or_equal(op0: r2u2_int, op1: r2u2_int) -> (result: r2u2_int)
    ensures
        result == 0 || result == 1,
        op0 <= op1 ==> result == 1,
        op0 > op1 ==> result == 0,
{
    if op0 <= op1 {
        return 1;
    } else {
        return 0;
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_less_than_or_equal(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_int)
{
    if (op0 < op1) || (float_equal(op0, op1) == 1) {
        return 1;
    } else {
        return 0;
    }
}

#[inline(always)]
fn integer_negative(op: r2u2_int) -> (result: (r2u2_int, r2u2_bool))
    ensures
        result.0 == -1 * op || result.0 == r2u2_int::MAX,
        result.0 <= r2u2_int::MAX,
        result.0 >= r2u2_int::MIN,
        -1 * op > r2u2_int::MAX ==> result.0 == r2u2_int::MAX,
        (-1 * op > r2u2_int::MAX || -1 * op < r2u2_int::MIN) ==> result.1 == true,
        (-1 * op <= r2u2_int::MAX && -1 * op >= r2u2_int::MIN) ==> result.1 == false,
{
    assert((-1 * r2u2_int::MAX) >= r2u2_int::MIN);
    if op == r2u2_int::MIN {
        return (r2u2_int::MAX, true);
    } else {
        return (-op, false);
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_negative(op: r2u2_float) -> (result: r2u2_float)
{
    return -op;
}

#[inline(always)]
fn integer_add(op0: r2u2_int, op1: r2u2_int) -> (result: (r2u2_int, r2u2_bool))
    ensures 
        result.0 == op0 + op1 || result.0 == r2u2_int::MIN || result.0 == r2u2_int::MAX,
        result.0 <= r2u2_int::MAX,
        result.0 >= r2u2_int::MIN,
        op0 + op1 > r2u2_int::MAX ==> result.0 == r2u2_int::MAX,
        op0 + op1 < r2u2_int::MIN ==> result.0 == r2u2_int::MIN,
        (op0 + op1 >= r2u2_int::MIN && op0 + op1 <= r2u2_int::MAX) ==> (result.0 == op0 + op1),
        (op0 + op1 > r2u2_int::MAX || op0 + op1 < r2u2_int::MIN) ==> (result.1 == true),
        (op0 + op1 <= r2u2_int::MAX && op0 + op1 >= r2u2_int::MIN) ==> (result.1 == false),
{
    match op0.checked_add(op1) {
        Some(n) => { return (n, false); },
        None => {
            if op0 < 0 && op1 < 0 {
                return (r2u2_int::MIN, true);
            } else {
                return (r2u2_int::MAX, true);
            }
        },
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_add(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_float)
{
    return op0 + op1;
}

#[inline(always)]
fn integer_subtract(op0: r2u2_int, op1: r2u2_int) -> (result: (r2u2_int, r2u2_bool))
    ensures 
        result.0 == op0 - op1 || result.0 == r2u2_int::MIN || result.0 == r2u2_int::MAX,
        result.0 <= r2u2_int::MAX,
        result.0 >= r2u2_int::MIN,
        op0 - op1 > r2u2_int::MAX ==> result.0 == r2u2_int::MAX,
        op0 - op1 < r2u2_int::MIN ==> result.0 == r2u2_int::MIN,
        (op0 - op1 >= r2u2_int::MIN && op0 - op1 <= r2u2_int::MAX) ==> (result.0 == op0 - op1),
        (op0 - op1 > r2u2_int::MAX || op0 - op1 < r2u2_int::MIN) ==> (result.1 == true),
        (op0 - op1 <= r2u2_int::MAX && op0 - op1 >= r2u2_int::MIN) ==> (result.1 == false),
{
    match op0.checked_sub(op1) {
        Some(n) => { return (n, false); },
        None => {
            if op0 < 0 && op1 > 0 {
                return (r2u2_int::MIN, true);
            } else {
                return (r2u2_int::MAX, true);
            }
        },
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_subtract(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_float)
{
    return op0 - op1;
}

#[inline(always)]
fn integer_multiply(op0: r2u2_int, op1: r2u2_int) -> (result: (r2u2_int, r2u2_bool)) by (nonlinear_arith)
    ensures 
        result.0 == op0 * op1 || result.0 == r2u2_int::MIN || result.0 == r2u2_int::MAX,
        result.0 <= r2u2_int::MAX,
        result.0 >= r2u2_int::MIN,
        op0 * op1 > r2u2_int::MAX ==> result.0 == r2u2_int::MAX,
        op0 * op1 < r2u2_int::MIN ==> result.0 == r2u2_int::MIN,
        (op0 * op1 > r2u2_int::MIN && op0 * op1 < r2u2_int::MAX) ==> (result.0 == op0 * op1),
        (op0 * op1 > r2u2_int::MAX || op0 * op1 < r2u2_int::MIN) ==> (result.1 == true),
        (op0 * op1 <= r2u2_int::MAX && op0 * op1 >= r2u2_int::MIN) ==> (result.1 == false),
{
    match op0.checked_mul(op1) {
        Some(n) => { return (n, false); },
        None => {
            if (op0 < 0 && op1 > 0) || (op0 > 0 && op1 < 0){
                return (r2u2_int::MIN, true);
            } else {
                return (r2u2_int::MAX, true);
            }
        },
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_multiply(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_float)
{
    return op0 * op1;
}

#[verifier::external] // Verus doesn't support divide functionality 
#[inline(always)]
fn integer_divide(op0: r2u2_int, op1: r2u2_int) -> (result: (r2u2_int, r2u2_bool))
{
    match op0.checked_div(op1) {
        Some(n) => { return (n, false); },
        None => {
            if op1 == 0 {
                return (0, true);
            }
            else if (op0 < 0 && op1 > 0) || (op0 > 0 && op1 < 0){
                return (r2u2_int::MIN, true);
            } else {
                return (r2u2_int::MAX, true);
            }
        },
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_divide(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_float)
{
    return op0 / op1;
}

#[verifier::external] // Verus doesn't support mod functionality 
#[inline(always)]
fn integer_mod(op0: r2u2_int, op1: r2u2_int) -> (result: (r2u2_int, r2u2_bool))
{
    if op1 == 0 {
        return (0, true);
    } else {
        return (op0 % op1, false);
    }
}

#[verifier::external] // Verus doesn't support mod functionality (i.e., op0 % 2)
#[inline(always)]
fn integer_power(op0: r2u2_int, op1: r2u2_int) -> (result: (r2u2_int, r2u2_bool))
{
    // Note that 0^0 = 0 with checked_pow
    match op0.checked_pow(op1 as u32) {
        Some(n) => { return (n, false); },
        None => {
            if op0 < 0 && ((op0 % 2) != 0){
                return (r2u2_int::MIN, true);
            } else {
                return (r2u2_int::MAX, true);
            }
        },
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_power(op0: r2u2_float, op1: r2u2_float) -> (result: r2u2_float)
{
    return pow(op0, op1);
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn integer_square_root(op: r2u2_int) -> (result: r2u2_int)
{
    match op.checked_isqrt() {
        Some(n) => {return n;}
        None => {
            return 0;
        }
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_square_root(op: r2u2_float) -> (result: r2u2_float)
{
    return sqrt(op);
}

#[inline(always)]
fn integer_absolute_value(op: r2u2_int) -> (result: (r2u2_int, r2u2_bool))
    ensures
        result.0 >= 0,
        result.0 == op || result.0 == r2u2_int::MAX || result.0 == -1 * op,
        (-1 * op > r2u2_int::MAX) ==> result.1 == true,
        (-1 * op <= r2u2_int::MAX) ==> result.1 == false,
{
    if op < 0 {
        return integer_negative(op);
    } else {
        return (op, false);
    }
}

#[verifier::external] // Verus doesn't support evaluation of floats 
#[inline(always)]
fn float_absolute_value(op: r2u2_float) -> (result: r2u2_float)
{
    if op < 0.0 {
        return -1.0 * op;
    } else {
        return op;
    }
}

}