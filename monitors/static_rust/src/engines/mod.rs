use super::{memory::monitor::*, internals::types::*};
use future_time::*;
use booleanizer::*;

pub const R2U2_ENG_NA: u8 = 0; // Null instruction tag - acts as ENDSEQ
pub const R2U2_ENG_SY: u8 = 1; // System commands - reserved for monitor control
pub const R2U2_ENG_CG: u8 = 2; // Immediate Configuration Directive
pub const R2U2_ENG_AT: u8 = 3; // Original Atomic Checker
pub const R2U2_ENG_TL: u8 = 4; // MLTL Temporal logic engine
pub const R2U2_ENG_BZ: u8 = 5; // Booleanizer

mod future_time;
mod booleanizer;

// Runs R2U2 for a single time step
pub fn r2u2_step(monitor: &mut Monitor){
    // Run booleanizer instructions (once)
    while monitor.bz_program_count.curr_program_count <= monitor.bz_program_count.max_program_count {
        bz_update(monitor);
        monitor.bz_program_count.curr_program_count = monitor.bz_program_count.curr_program_count + 1;
    }
    monitor.bz_program_count.curr_program_count = 0;
    // Run mltl instructions (currently just supporting future time)
    let start_time = monitor.time_stamp;
    while start_time == monitor.time_stamp{
        while monitor.mltl_program_count.curr_program_count <= monitor.mltl_program_count.max_program_count {
            mltl_ft_update(monitor);
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
                monitor.time_stamp = monitor.time_stamp + 1;
                monitor.mltl_program_count.curr_program_count = 0;
                monitor.progress = MonitorProgressState::FirstLoop;
            }
        }
    }

}