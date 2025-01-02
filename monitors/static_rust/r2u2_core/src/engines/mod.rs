use crate::internals::types::*;
use crate::memory::monitor::*;
use mltl::*;
use booleanizer::*;

mod mltl;
mod booleanizer;

#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
use crate::internals::debug::*;

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

// pub const R2U2_ENG_NA: u8 = 0; // Null instruction tag - acts as ENDSEQ
// pub const R2U2_ENG_SY: u8 = 1; // System commands - reserved for monitor control
pub const R2U2_ENG_CG: u8 = 2; // Immediate Configuration Directive
// pub const R2U2_ENG_AT: u8 = 3; // Original Atomic Checker
pub const R2U2_ENG_TL: u8 = 4; // MLTL Temporal logic engine
pub const R2U2_ENG_BZ: u8 = 5; // Booleanizer

// Runs R2U2 for a single time step
pub fn r2u2_step(monitor: &mut Monitor) -> r2u2_bool{
    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
    debug_print!("-------Step {}-------", monitor.time_stamp);
    //Reset output buffer
    monitor.output_buffer_idx = 0;
    // Run booleanizer instructions (once)
    while monitor.bz_program_count.curr_program_count < monitor.bz_program_count.max_program_count {
        bz_update(monitor);
        monitor.bz_program_count.curr_program_count = monitor.bz_program_count.curr_program_count + 1;
    }
    monitor.bz_program_count.curr_program_count = 0;
    // Run mltl instructions (currently just supporting future time)
    let start_time = monitor.time_stamp;
    while start_time == monitor.time_stamp{
        while monitor.mltl_program_count.curr_program_count < monitor.mltl_program_count.max_program_count {
            mltl_update(monitor);
            monitor.mltl_program_count.curr_program_count = monitor.mltl_program_count.curr_program_count + 1;
        }
        match monitor.progress {
            MonitorProgressState::FirstLoop => {
                // First pass complete, rerun program counter to check for progress
                monitor.mltl_program_count.curr_program_count = 0;
                monitor.progress = MonitorProgressState::ReloopNoProgress;
            }
            MonitorProgressState::ReloopWithProgress => {
                // Progress made this loop, rerun program counter
                monitor.mltl_program_count.curr_program_count = 0;
                monitor.progress = MonitorProgressState::ReloopNoProgress;
            }
            MonitorProgressState::ReloopNoProgress => {
                // End of timestamp, setup for next step
                match monitor.time_stamp.checked_add(1) {
                    Some(n) => { 
                        monitor.time_stamp = n;
                        monitor.mltl_program_count.curr_program_count = 0;
                        monitor.progress = MonitorProgressState::FirstLoop; 
                    },
                    None => {
                        // timestamp overflowed; therefore reset entire monitor (simple safety measure, but could be improved)
                        monitor.reset();
                    },
                }
            }
        }
    }
    return !monitor.overflow_error;
}