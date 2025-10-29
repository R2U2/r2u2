use crate::instructions::{booleanizer::BooleanizerInstruction, mltl::MLTLInstruction};
use crate::internals::types::*;
use crate::memory::scq::{SCQMemoryArena, SCQCtrlBlock};

#[cfg(feature = "aux_string_specs")]
use crate::instructions::aux_info::*;


use crate::internals::bounds::*;
    
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

/// Struct to contain monitor information
pub struct Monitor{
    pub time_stamp: r2u2_time,
    pub progress: MonitorProgressState,
    pub bz_program_count: ProgramCount,
    pub bz_instruction_table: [BooleanizerInstruction; R2U2_MAX_BZ_INSTRUCTIONS],
    pub mltl_program_count: ProgramCount,
    pub mltl_instruction_table: [MLTLInstruction; R2U2_MAX_TL_INSTRUCTIONS],
    #[cfg(feature = "aux_string_specs")]
    pub formula_aux_string_table: [FormulaAuxiliaryInfo; R2U2_MAX_FORMULAS],
    #[cfg(feature = "aux_string_specs")]
    pub contract_aux_string_table: [ContractAuxiliaryInfo; R2U2_MAX_CONTRACTS],
    pub queue_arena: SCQMemoryArena,
    pub signal_buffer: [r2u2_value; R2U2_MAX_SIGNALS],
    pub value_buffer: [r2u2_value; R2U2_MAX_BZ_INSTRUCTIONS],
    pub atomic_buffer: [r2u2_bool; R2U2_MAX_ATOMICS],
    pub output_buffer: [r2u2_output; R2U2_MAX_OUTPUT_VERDICTS],
    pub output_buffer_idx: usize,
    #[cfg(feature = "aux_string_specs")]
    pub contract_buffer: [r2u2_contract; R2U2_MAX_OUTPUT_CONTRACTS],
    #[cfg(feature = "aux_string_specs")]
    pub contract_buffer_idx: usize,
    pub overflow_error: r2u2_bool,
}


impl Default for Monitor{
    fn default() -> Self {
        return Monitor {
            time_stamp: 0,
            progress: MonitorProgressState::FirstLoop,
            bz_program_count: ProgramCount{curr_program_count: 0, max_program_count: 0},
            bz_instruction_table: [BooleanizerInstruction::empty_instr(); R2U2_MAX_BZ_INSTRUCTIONS],
            mltl_program_count: ProgramCount{curr_program_count: 0, max_program_count: 0},
            mltl_instruction_table: [MLTLInstruction::empty_instr(); R2U2_MAX_TL_INSTRUCTIONS],
            #[cfg(feature = "aux_string_specs")]
            formula_aux_string_table: [FormulaAuxiliaryInfo::default(); R2U2_MAX_FORMULAS],
            #[cfg(feature = "aux_string_specs")]
            contract_aux_string_table: [ContractAuxiliaryInfo::default(); R2U2_MAX_CONTRACTS],
            queue_arena: SCQMemoryArena::initialize(),
            signal_buffer: [r2u2_value::default(); R2U2_MAX_SIGNALS],
            value_buffer: [r2u2_value::default(); R2U2_MAX_BZ_INSTRUCTIONS],
            atomic_buffer: [false; R2U2_MAX_ATOMICS],
            output_buffer: [r2u2_output::default(); R2U2_MAX_OUTPUT_VERDICTS],
            output_buffer_idx: 0,
            #[cfg(feature = "aux_string_specs")]
            contract_buffer: [r2u2_contract::default(); R2U2_MAX_OUTPUT_CONTRACTS],
            #[cfg(feature = "aux_string_specs")]
            contract_buffer_idx: 0,
            overflow_error: false,
        }
    }
}

impl Monitor{
    pub fn clock_reset(&mut self) {
        self.time_stamp = 0;
        self.progress = MonitorProgressState::FirstLoop;
        self.bz_program_count.curr_program_count = 0;
        self.mltl_program_count.curr_program_count = 0;
        for elem in self.queue_arena.queue_mem.iter_mut() {
            *elem = r2u2_verdict::default()
        }
    }
    pub fn reset(&mut self) {
        self.clock_reset();
        self.bz_program_count.max_program_count = 0;
        self.bz_program_count.max_program_count = 0;
        for elem in self.queue_arena.control_blocks.iter_mut() {
            *elem = SCQCtrlBlock::default();
        }
    }
}