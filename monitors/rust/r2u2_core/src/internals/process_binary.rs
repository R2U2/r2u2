use crate::memory::scq::SCQCtrlBlock;
use crate::{engines, memory};
use crate::instructions::{booleanizer::*, mltl::*};

#[cfg(feature = "aux_string_specs")]
use crate::instructions::aux::AuxiliaryInfo;


#[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
use crate::internals::debug::*;
#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

pub fn process_binary_file(spec_file: &[u8], monitor: &mut memory::monitor::Monitor){
    let mut offset = spec_file[0] as usize;

    while spec_file[offset] != 0 {
        // Configure Instructions
        if (spec_file[offset + 1] == engines::R2U2_ENG_CG as u8) && (spec_file[offset + 2] == engines::R2U2_ENG_TL as u8){
            let instr = MLTLInstruction::set_from_binary(&spec_file[offset+3..]);
            mltl_configure_instruction_dispatch(instr, monitor);
        }
        // Booleanizer Instructions
        else if spec_file[offset + 1] == engines::R2U2_ENG_BZ as u8{
            let instr = BooleanizerInstruction::set_from_binary(&spec_file[offset+2..]);
            match instr.opcode{
                // Special case: ICONST and FCONST only need to be run once since they load constants
                BZ_OP_ICONST=> {
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("BZ ICONST");
                    let op_const = BooleanizerInstruction::get_param1_int_from_binary(&spec_file[offset+2..]);
                    monitor.value_buffer[instr.memory_reference as usize].i = op_const;
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("b{} = {}", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].i);
                }
                BZ_OP_FCONST=> {
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("BZ FCONST");
                    let op_const = BooleanizerInstruction::get_param1_float_from_binary(&spec_file[offset+2..]);
                    monitor.value_buffer[instr.memory_reference as usize].f = op_const;
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("b{} = {}", instr.memory_reference, monitor.value_buffer[instr.memory_reference as usize].f);
                }
                _ => {
                    // Store instruction in table
                    monitor.bz_instruction_table[monitor.bz_program_count.max_program_count] = instr;
                    monitor.bz_program_count.max_program_count += 1;
                }
            }
        }
        // Temporal Logic Instructions
        else if spec_file[offset+1] == engines::R2U2_ENG_TL as u8{
            let instr = MLTLInstruction::set_from_binary(&spec_file[offset+2..]);
            // Store instruction in table
            monitor.mltl_instruction_table[monitor.mltl_program_count.max_program_count] = instr;
            monitor.mltl_program_count.max_program_count += 1;
        }
        offset = offset + (spec_file[offset] as usize);
    }

    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]{
    // Print output of booleanizer table
    let mut i = 0;
    while i < monitor.bz_program_count.max_program_count{
        print_bz_instruction(monitor.bz_instruction_table[i]);
        i = i + 1;
    }
    }

    // Iterate through mltl table
    let mut i = 0;
    while i < monitor.mltl_program_count.max_program_count{
        // For future time, we never need information from [0, lb]
        if monitor.mltl_instruction_table[i].opcode == MLTL_OP_FT_UNTIL || 
            monitor.mltl_instruction_table[i].opcode == MLTL_OP_FT_RELEASE {
                let queue: &mut SCQCtrlBlock = &mut monitor.queue_arena.control_blocks[monitor.mltl_instruction_table[i].memory_reference as usize];
                queue.next_time = queue.temporal_block.lower_bound;
            }
        // Print output of mltl table
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        print_mltl_instruction(monitor.mltl_instruction_table[i]);
        i += 1;
    }

    #[cfg(feature = "aux_string_specs")]{
        let mut i = 0;
        let mut length;
        offset += 1;
        while { // Rust do-while loop
            match spec_file[offset] as char {
                'C' => { // Contract auxiliary info
                    (monitor.aux_string_table[i], length) = AuxiliaryInfo::set_contract(&spec_file[offset..]);
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("Mapping contract: {} to {}, {}, and {}", monitor.aux_string_table[i].spec_str, monitor.aux_string_table[i].spec_0,
                    monitor.aux_string_table[i].spec_1,  monitor.aux_string_table[i].spec_2);
                },
                'F' => { // Function auxiliary info
                    (monitor.aux_string_table[i], length) = AuxiliaryInfo::set_function(&spec_file[offset..]);
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("Mapping function: {} to {}", monitor.aux_string_table[i].spec_str, monitor.aux_string_table[i].spec_0);
                },
                _ => { 
                    #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                    debug_print!("Invalid aux type '{}`", spec_file[offset] as char);
                    length = 0;
                }
            }

            offset = offset + length + 1;
            i += 1;
            
            spec_file[offset] != 0 // Condition to loop again
        } {}
    }
}