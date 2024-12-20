#![no_std]

use internals::types::*;

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

mod instructions;
mod internals;
mod engines;
mod memory;

pub use internals::process_binary::process_binary_file;
pub use memory::monitor::Monitor;
pub use engines::r2u2_step;

pub fn load_bool_signal(monitor: &mut memory::monitor::Monitor, index: usize, value: r2u2_bool){
    if monitor.bz_program_count.max_program_count == 0 {
        monitor.atomic_buffer[index] = value;
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        internals::debug::debug_print!("Loaded atomic in directly at {}: {}", index, monitor.atomic_buffer[index]);
    } else{
        monitor.signal_buffer[index].i = value as r2u2_int;
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        internals::debug::debug_print!("Loading in signal {}: {}", index, monitor.signal_buffer[index].i != 0);
    }
}

pub fn load_int_signal(monitor: &mut memory::monitor::Monitor, index: usize, value: r2u2_int){
    if monitor.bz_program_count.max_program_count == 0 {
        monitor.atomic_buffer[index] = if value == 0 {false} else {true};
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        internals::debug::debug_print!("Loaded atomic in directly at {}: {}", index, monitor.atomic_buffer[index]);
    } else{
        monitor.signal_buffer[index].i = value;
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        internals::debug::debug_print!("Loading in signal {}: {}", index, monitor.signal_buffer[index].i);
    }
}

pub fn load_float_signal(monitor: &mut memory::monitor::Monitor, index: usize, value: r2u2_float){
    if monitor.bz_program_count.max_program_count == 0 {
        monitor.atomic_buffer[index] = if value == 0.0 {false} else {true};
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        internals::debug::debug_print!("Loaded atomic in directly at {}: {}", index, monitor.atomic_buffer[index]);
    } else{
        monitor.signal_buffer[index].f = value;
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        internals::debug::debug_print!("Loading in signal {}: {}", index, monitor.signal_buffer[index].f);

    }
}

pub fn load_string_signal(monitor: &mut memory::monitor::Monitor, index: usize, value: &str){
    if monitor.bz_program_count.max_program_count == 0 {
        monitor.atomic_buffer[index] = if value.parse::<r2u2_int>().expect("Please provide a 0 or 1") == 0 {false} else {true};
        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
        internals::debug::debug_print!("Loaded atomic in directly at {}: {}", index, monitor.atomic_buffer[index]);
    } else{
        match value.parse::<r2u2_int>() {
            Ok(n) => {
                monitor.signal_buffer[index].i = n;
                #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                internals::debug::debug_print!("Loading in signal {}: {}", index, monitor.signal_buffer[index].i);
                match value.parse::<r2u2_float>() {
                    Ok(n) => {
                        monitor.signal_buffer[index].f = n;
                        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                        internals::debug::debug_print!("Loading in signal {}: {}", index, monitor.signal_buffer[index].f);
                    },
                    Err(_e) => ()
                }
            }
            Err(_e) => 
                match value.parse::<r2u2_float>() {
                    Ok(n) => {
                        monitor.signal_buffer[index].f = n;
                        #[cfg(any(feature = "debug_print_semihosting", feature = "debug_print_std"))]
                        internals::debug::debug_print!("Loading in signal {}: {}", index, monitor.signal_buffer[index].f);
                    },
                    Err(_e) => panic!("Please provide a valid number!")
                }
        }
    }
}

pub fn get_output_buffer(monitor: &memory::monitor::Monitor) -> &[r2u2_output]{
    return &monitor.output_buffer[0..monitor.output_buffer_idx];
}

pub fn get_overflow_error(monitor: &memory::monitor::Monitor) -> r2u2_bool {
    return monitor.overflow_error;
}

pub fn reset_overflow_error(monitor: &mut memory::monitor::Monitor){
    monitor.overflow_error = false;
}