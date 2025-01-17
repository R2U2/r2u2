#![no_std]

use internals::types::*;
use internals::process_binary::process_binary_file;
use memory::monitor::Monitor;
use engines::r2u2_step;

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

mod instructions;
mod internals;
mod engines;
mod memory;

pub use internals::types::r2u2_output;
pub use internals::types::r2u2_verdict;
pub use internals::bounds::{R2U2_MAX_SPECS,R2U2_MAX_SIGNALS,R2U2_MAX_ATOMICS,R2U2_MAX_BZ_INSTRUCTIONS,R2U2_MAX_TL_INSTRUCTIONS,R2U2_TOTAL_QUEUE_MEM};

/// Get runtime monitor
/// 
/// # Arguments
/// 
/// * `spec_file` - A reference to a vector or array of u8 from the specification compiled by C2PO
/// 
/// # Returns
/// 
/// A new `Monitor` with the specifications loaded
/// 
/// # Examples
/// 
/// ```
/// let spec_file: Vec<u8> = fs::read(spec_file_path).expect("Error opening specification file");
/// let mut monitor = r2u2_core::get_monitor(&spec_file);
/// ```
/// 
pub fn get_monitor(spec_file: &[u8]) -> Monitor{
    let mut monitor = Monitor::default();
    process_binary_file(spec_file, &mut monitor);
    return monitor;
}

/// Update specification binary file
/// 
/// # Arguments
/// 
/// * `spec_file` - A reference to a vector or array of u8 from the specification compiled by C2PO
/// * `monitor` - A reference to a monitor
/// 
pub fn update_binary_file(spec_file: &[u8], monitor: &mut Monitor){
    process_binary_file(spec_file, monitor);
}

/// Take a step with runtime monitor
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// 
/// # Returns
/// 
/// A `bool` indicating if successful (true) or overflow occured (false)
/// 
pub fn monitor_step(monitor: &mut Monitor) -> r2u2_bool{
    r2u2_step(monitor)
}

/// Load boolean signal
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// * `index` - Signal index\mapping as specified when compiled with C2PO
/// * `value` - The boolean value to load
/// 
pub fn load_bool_signal(monitor: &mut Monitor, index: usize, value: r2u2_bool){
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

/// Load integer signal
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// * `index` - Signal index\mapping as specified when compiled with C2PO
/// * `value` - The integer value to load
/// 
pub fn load_int_signal(monitor: &mut Monitor, index: usize, value: r2u2_int){
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

/// Load float signals
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// * `index` - Signal index\mapping as specified when compiled with C2PO
/// * `value` - The float value to load
/// 
pub fn load_float_signal(monitor: &mut Monitor, index: usize, value: r2u2_float){
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

/// Load signal as string (decoded as integer, float, or boolean)
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// * `index` - Signal index\mapping as specified when compiled with C2PO
/// * `value` - The string value to load (gets encoded as float, integer, or boolean as applicable)
/// 
pub fn load_string_signal(monitor: &mut Monitor, index: usize, value: &str){
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

/// Get output buffer
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// 
/// # Returns
/// 
/// A reference to an array of r2u2_outputs from the last call of monitor_step()
/// 
/// # Examples
/// 
/// ```
/// let mut monitor = r2u2_core::get_monitor(&spec_file);
/// for out in r2u2_core::get_output_buffer(&mut monitor).iter() {
///     println!("{}:{},{}", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
/// }
/// ```
/// 
pub fn get_output_buffer(monitor: &Monitor) -> &[r2u2_output]{
    return &monitor.output_buffer[0..monitor.output_buffer_idx];
}

/// Get overflow error flag
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// 
/// # Returns
/// 
/// A `bool` indicating if overflow (true) or no overflow occured (false)
/// 
pub fn get_overflow_error(monitor: &Monitor) -> r2u2_bool {
    return monitor.overflow_error;
}

/// Reset overflow flag
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// 
pub fn reset_overflow_error(monitor: &mut Monitor){
    monitor.overflow_error = false;
}