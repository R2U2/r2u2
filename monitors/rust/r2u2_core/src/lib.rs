//! # Library for r2u2_core
//!
//!  R2U2: A stream-based runtime monitor written in `#![no_std]` that reasons over Mission-Time Linear
//! Temporal Logic (MLTL) specifications compiled with the Configuration Compiler for Property Organization (C2PO).
//!
//! ## Optional Features:
//! 
//! - `aux_string_specs`: Enable Assume-Guarantee Contract status output and string auxiliary specification naming. This feature
//! enables the following:
//!     - **[r2u2_contract]** type
//!     - **[r2u2_output::spec_str]** member of the **[r2u2_output]** type
//!     - **[get_contract_buffer]** function
//!     - **[AGC_INACTIVE]**, **[AGC_INVALID]**, and **[AGC_VERIFIED]** constants
//! - `debug_print_std`: Debug printing to terminal (i.e., `println!`)
//! - `debug_print_semihosting`: Debug printing utilizing GDB debugger of microcontroller (i.e., `hprintln!`)
//! 
//! ## Usage:
//! 1. A monitor must be created utilizing **[get_monitor]**. The specification file from C2PO must be passed by reference as
//! `&[u8]`. The specifications can later be updated with **[update_binary_file]**; this will also reset the monitor to its intial state.
//! 2. Signals must be loaded in according to the mapping specified when compiling the specification file through **[load_bool_signal]**,
//! **[load_float_signal]**, **[load_int_signal]**, and **[load_string_signal]**.
//! 3. Run the monitor for a single timestep with **[monitor_step]**.
//! 4. Get output data through **[get_output_buffer]** and **[get_contract_buffer]**.
//! 5. Repeat steps 2-4. (Optionally check for overflow with the output of **[monitor_step]** or **[get_overflow_error]**.)
//! 
//! For details on compiling specifications with C2PO, refer to [README](https://crates.io/crates/r2u2_core).

#![no_std]

use internals::types::*;
use internals::process_binary::process_binary_file;
use engines::r2u2_engine_step;

#[cfg(feature = "debug_print_semihosting")]
use cortex_m_semihosting::hprintln;

#[cfg(feature = "debug_print_std")]
use libc_print::std_name::println;

mod instructions;
mod internals;
mod engines;
mod memory;

pub use internals::types::{r2u2_output,r2u2_verdict};
pub use memory::monitor::Monitor;
#[cfg(feature = "aux_string_specs")]
pub use internals::types::{r2u2_contract, AGC_INACTIVE, AGC_INVALID, AGC_VERIFIED};
#[cfg(feature = "aux_string_specs")]
pub use internals::bounds::{R2U2_MAX_OUTPUT_CONTRACTS, R2U2_AUX_MAX_FORMULAS, R2U2_AUX_MAX_CONTRACTS};
pub use internals::bounds::{R2U2_MAX_OUTPUT_VERDICTS,R2U2_MAX_SIGNALS,R2U2_MAX_ATOMICS,R2U2_MAX_BZ_INSTRUCTIONS,R2U2_MAX_TL_INSTRUCTIONS,R2U2_MAX_QUEUE_SLOTS,R2U2_FLOAT_EPSILON};

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

/// Update specification binary file (and reset monitor)
/// 
/// # Arguments
/// 
/// * `spec_file` - A reference to a vector or array of u8 from the specification compiled by C2PO
/// * `monitor` - A reference to a monitor
/// 
pub fn update_binary_file(spec_file: &[u8], monitor: &mut Monitor){
    monitor.reset();
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
    r2u2_engine_step(monitor)
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
        monitor.atomic_buffer[index] = value != 0;
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
        monitor.atomic_buffer[index] = value >= R2U2_FLOAT_EPSILON || value <= -R2U2_FLOAT_EPSILON;
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
        monitor.atomic_buffer[index] = value.parse::<r2u2_int>().expect("Please provide a 0 or 1") != 0;
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

/// Get output verdict buffer
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
/// for out in r2u2_core::get_output_buffer(&monitor) {
///     println!("{}:{},{}", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
/// }
/// ```
/// 
pub fn get_output_buffer(monitor: &Monitor) -> &[r2u2_output]{
    return &monitor.output_buffer[0..monitor.output_buffer_idx];
}

#[cfg(feature = "aux_string_specs")]
/// Get Assume-Guarantee Contract (AGC) buffer
/// 
/// # Arguments
/// 
/// * `monitor` - A reference to a monitor
/// 
/// # Returns
/// 
/// A reference to an array of r2u2_contracts from the last call of monitor_step()
/// 
/// # Examples
/// 
/// ```
/// let mut monitor = r2u2_core::get_monitor(&spec_file);
/// for out in r2u2_core::get_contract_buffer(&monitor) {
///     println!("Contract {} {} at {}", out.spec_str, if out.status == r2u2_core::AGC_VERIFIED {"verified"} else if out.status == r2u2_core::AGC_INVALID {"invalid"} else {"inactive"}, out.time);
/// }
/// ```
/// 
pub fn get_contract_buffer(monitor: &Monitor) -> &[r2u2_contract]{
    return &monitor.contract_buffer[0..monitor.contract_buffer_idx];
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