use crate::instructions::{booleanizer::*, mltl::*};
use crate::internals::types::*;
use crate::memory::scq::SCQMemoryArena;

#[cfg(feature = "aux_string_specs")]
use crate::instructions::aux::*;

#[cfg(feature = "configurable")]
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

#[cfg(feature = "configurable")]
pub struct Monitor{
    pub time_stamp: r2u2_time,
    pub progress: MonitorProgressState,
    pub bz_program_count: ProgramCount,
    pub bz_instruction_table: [BooleanizerInstruction; R2U2_MAX_BZ_INSTRUCTIONS],
    pub mltl_program_count: ProgramCount,
    pub mltl_instruction_table: [MLTLInstruction; R2U2_MAX_TL_INSTRUCTIONS],
    #[cfg(feature = "aux_string_specs")]
    pub aux_string_table: [AuxiliaryInfo; R2U2_MAX_SPECS],
    pub queue_arena: SCQMemoryArena,
    pub signal_buffer: [r2u2_value; R2U2_MAX_SIGNALS],
    pub value_buffer: [r2u2_value; R2U2_MAX_BZ_INSTRUCTIONS],
    pub atomic_buffer: [r2u2_bool; R2U2_MAX_ATOMICS],
    pub output_buffer: [r2u2_output; R2U2_MAX_SPECS*2], //output_buffer may contain upto 2 verdicts per spec at each timestep due to propagation delay
    pub output_buffer_idx: usize,
    #[cfg(feature = "aux_string_specs")]
    pub contract_buffer: [r2u2_contract; R2U2_MAX_SPECS], //contract_buffer may contain upto 2 verdicts per contract and there are 3 specs per contract
    #[cfg(feature = "aux_string_specs")]
    pub contract_buffer_idx: usize,
    pub overflow_error: r2u2_bool,
}

#[cfg(feature = "configurable")]
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
            aux_string_table: [AuxiliaryInfo::default(); if cfg!(feature = "aux_string_specs") {R2U2_MAX_SPECS} else {0}],
            queue_arena: SCQMemoryArena::initialize(),
            signal_buffer: [r2u2_value::default(); R2U2_MAX_SIGNALS],
            value_buffer: [r2u2_value::default(); R2U2_MAX_BZ_INSTRUCTIONS],
            atomic_buffer: [false; R2U2_MAX_ATOMICS],
            output_buffer: [r2u2_output::default(); R2U2_MAX_SPECS*2],
            output_buffer_idx: 0,
            #[cfg(feature = "aux_string_specs")]
            contract_buffer: [r2u2_contract::default(); R2U2_MAX_SPECS],
            #[cfg(feature = "aux_string_specs")]
            contract_buffer_idx: 0,
            overflow_error: false,
        }
    }
}

impl Monitor{
    pub fn reset(&mut self) {
        *self = Monitor::default();
    }
}

#[cfg(not(feature = "configurable"))]
pub struct Monitor{
    pub time_stamp: r2u2_time,
    pub progress: MonitorProgressState,
    pub bz_program_count: ProgramCount,
    pub bz_instruction_table: [BooleanizerInstruction; 256],
    pub mltl_program_count: ProgramCount,
    pub mltl_instruction_table: [MLTLInstruction; 256],
    #[cfg(feature = "aux_string_specs")]
    pub aux_string_table: [AuxiliaryInfo; if cfg!(feature = "aux_string_specs") {256*2} else {0}],
    pub queue_arena: SCQMemoryArena,
    pub signal_buffer: [r2u2_value; 256],
    pub value_buffer: [r2u2_value; 256],
    pub atomic_buffer: [r2u2_bool; 256],
    pub output_buffer: [r2u2_output; 256*2], //output_buffer may contain upto 2 verdicts per spec at each timestep due to propagation delay
    pub output_buffer_idx: usize,
    #[cfg(feature = "aux_string_specs")]
    pub contract_buffer: [r2u2_contract; 256], //contract_buffer may contain upto 2 verdicts per contract and there are 3 specs per contract
    #[cfg(feature = "aux_string_specs")]
    pub contract_buffer_idx: usize,
    pub overflow_error: r2u2_bool,
}

#[cfg(not(feature = "configurable"))]
impl Default for Monitor{
    fn default() -> Self {
        return Monitor {
            time_stamp: 0,
            progress: MonitorProgressState::FirstLoop,
            bz_program_count: ProgramCount{curr_program_count: 0, max_program_count: 0},
            bz_instruction_table: [BooleanizerInstruction::empty_instr(); 256],
            mltl_program_count: ProgramCount{curr_program_count: 0, max_program_count: 0},
            mltl_instruction_table: [MLTLInstruction::empty_instr(); 256],
            #[cfg(feature = "aux_string_specs")]
            aux_string_table: [AuxiliaryInfo::default(); R2U2_MAX_SPECS],
            queue_arena: SCQMemoryArena::initialize(),
            signal_buffer: [r2u2_value::default(); 256],
            value_buffer: [r2u2_value::default(); 256],
            atomic_buffer: [false; 256],
            output_buffer: [r2u2_output::default(); 256*2],
            output_buffer_idx: 0,
            #[cfg(feature = "aux_string_specs")]
            contract_buffer: [r2u2_contract::default(); 256], //contract_buffer may contain upto 2 verdicts per contract and there are 3 specs per contract
            #[cfg(feature = "aux_string_specs")]
            contract_buffer_idx: usize,
            overflow_error: false,
        }
    }
}