use super::super::{engines, instructions, memory};
use super::super::internals::debug::*;

#[cfg(embedded)]
use cortex_m_semihosting::hprintln;


pub fn process_binary_file(spec_file: &[u8], monitor: &mut memory::monitor::Monitor){
    let mut offset = spec_file[0] as usize;

    while spec_file[offset] != 0 {
        // Configure Instructions
        if (spec_file[offset + 1] == engines::R2U2_ENG_CG as u8) && (spec_file[offset + 2] == engines::R2U2_ENG_TL as u8){
            // To-Do: Check if this requires any extra memory
            let instr = instructions::mltl::MLTLInstruction::set_from_binary(&spec_file[offset+3..]);
            instructions::mltl::mltl_configure_instruction_dispatch(instr, monitor);
            // need to dispatch configure instruction
        }
        // Booleanizer Instructions
        else if spec_file[offset+1] == engines::R2U2_ENG_BZ as u8{
            let instr = instructions::booleanizer::BooleanizerInstruction::set_from_binary(&spec_file[offset+2..]);
            // Store instruction in table
            monitor.bz_instruction_table[monitor.bz_program_count.max_program_count] = instr;
            monitor.bz_program_count.max_program_count = monitor.bz_program_count.max_program_count + 1;
        }
        // Temporal Logic Instructions
        else if spec_file[offset+1] == engines::R2U2_ENG_TL as u8{
            let instr = instructions::mltl::MLTLInstruction::set_from_binary(&spec_file[offset+2..]);
            // Store instruction in table
            monitor.mltl_instruction_table[monitor.mltl_program_count.max_program_count] = instr;
            monitor.mltl_program_count.max_program_count = monitor.mltl_program_count.max_program_count + 1;
        }
        offset = offset + (spec_file[offset] as usize);
    }
}

// BZ b0  iload  0 0
// BZ b1  iload  1 0
// BZ b2  iload  2 0
// TL n0  load   a0
// TL n1  not    n0
// TL n2  load   a1
// TL n3  not    n2
// TL n4  and    n1 n3
// TL n5  not    n4
// TL n6  global n5
// TL n7  return n6 0
// TL n8  load   a2
// TL n9  and    n2 n8
// TL n10 until  n0 n9
// TL n11 return n10 1
// CG TL DUOQ q0 |1|
// CG TL DUOQ q1 |1|
// CG TL DUOQ q2 |1|
// CG TL DUOQ q3 |1|
// CG TL DUOQ q4 |1|
// CG TL DUOQ q5 |1|
// CG TL DUOQ q6 |5|
// CG TL TEMP q6 [1, 2]
// CG TL DUOQ q7 |1|
// CG TL DUOQ q8 |1|
// CG TL DUOQ q9 |1|
// CG TL DUOQ q10 |5|
// CG TL TEMP q10 [0, 2]
// CG TL DUOQ q11 |1|
// F __f0__ 0
// F __f1__ 1