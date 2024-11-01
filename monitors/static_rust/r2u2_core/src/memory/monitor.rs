use crate::instructions::booleanizer;

use super::{super::{instructions::mltl, internals::{bounds::*, types::*}}, scq::SCQMemoryArena};

#[derive(PartialEq)]
pub enum MonitorProgressState {
    FirstLoop,
    ReloopNoProgress,
    ReloopWithProgress,
}

pub struct ProgramCount{
    pub curr_program_count: usize,
    pub max_program_count: usize,
}

pub struct Monitor{
    pub time_stamp: r2u2_time,
    pub progress: MonitorProgressState,
    pub bz_program_count: ProgramCount,
    pub bz_instruction_table: [booleanizer::BooleanizerInstruction; R2U2_MAX_BZ_INSTRUCTIONS],
    pub mltl_program_count: ProgramCount,
    pub mltl_instruction_table: [mltl::MLTLInstruction; R2U2_MAX_TL_INSTRUCTIONS],
    pub queue_arena: SCQMemoryArena,
    pub signal_buffer: [r2u2_value; R2U2_MAX_SIGNALS],
    pub value_buffer: [r2u2_value; R2U2_MAX_BZ_INSTRUCTIONS],
    pub atomic_buffer: [r2u2_bool; R2U2_MAX_ATOMICS],
    pub output_buffer: [r2u2_output; R2U2_MAX_SPECS*2], //output_buffer may contain upto 2 verdicts per spec at each timestep due to propagation delay
    pub output_buffer_idx: usize,
}

impl Default for Monitor{
    fn default() -> Self {
        return Monitor {
            time_stamp: 0,
            progress: MonitorProgressState::FirstLoop,
            bz_program_count: ProgramCount{curr_program_count: 0, max_program_count: 0},
            bz_instruction_table: [booleanizer::BooleanizerInstruction::empty_instr(); R2U2_MAX_BZ_INSTRUCTIONS],
            mltl_program_count: ProgramCount{curr_program_count: 0, max_program_count: 0},
            mltl_instruction_table: [mltl::MLTLInstruction::empty_instr(); R2U2_MAX_TL_INSTRUCTIONS],
            queue_arena: SCQMemoryArena::initialize(),
            signal_buffer: [r2u2_value::default(); R2U2_MAX_SIGNALS],
            value_buffer: [r2u2_value::default(); R2U2_MAX_BZ_INSTRUCTIONS],
            atomic_buffer: [false; R2U2_MAX_ATOMICS],
            output_buffer: [r2u2_output::default(); R2U2_MAX_SPECS*2],
            output_buffer_idx: 0,
        }
    }
}

impl Monitor{
    pub fn reset_clock(&mut self) {
        self.time_stamp = 0;
        self.progress = MonitorProgressState::FirstLoop;
        self.mltl_program_count.curr_program_count = 0;
    }
}