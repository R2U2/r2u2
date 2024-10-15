#![cfg_attr(embedded, no_std)]
#![cfg_attr(embedded, no_main)]



#[cfg(embedded)]
use panic_halt as _;

#[cfg(embedded)]
use cortex_m_rt::entry;
#[cfg(embedded)]
use cortex_m_semihosting::hprintln;

#[cfg(not(embedded))]
use std::env;
#[cfg(not(embedded))]
use std::fs;
#[cfg(not(embedded))]
use csv::{Reader, StringRecord};

mod instructions;
mod internals;
mod engines;
mod memory;

#[cfg(embedded)]
#[entry]
fn main() -> ! {
    hprintln!("Hello, world");
    internals::stm32_f3_discovery_usb_interface::read_binary_file();
    loop {}
}

#[cfg(not(embedded))]
fn main() {
    use internals::types::r2u2_float;

    const HELP: &str = "Usage: \t<configuration> [trace]
        configuration: path to monitor configuration binary
        trace: optional path to input CSV;\n";

    let args: Vec<String> = env::args().collect();

    if args.len() < 2 || args.len() > 3 {
        println!("{HELP}");
        return;
    }

    let spec_file_path = &args[1];

    let spec_file: Vec<u8> = fs::read(spec_file_path).expect("Error opening specification file");

    // if cfg!(target_endian = "big") {
    //     println!("Big endian");
    // } else {
    //     println!("Little endian");
    // }

    let mut monitor = memory::monitor::Monitor::initialize();
    internals::process_binary::process_binary_file(&spec_file, &mut monitor);

    // Print output of table
    let mut i = 0;
    while i < monitor.bz_program_count.max_program_count{
        internals::debug::print_bz_instruction(monitor.bz_instruction_table[i]);
        i = i + 1;
    }

    // Print output of table
    let mut i = 0;
    while i < monitor.mltl_program_count.max_program_count{
        internals::debug::print_mltl_instruction(monitor.mltl_instruction_table[i]);
        i = i + 1;
    }

    let signal_file_path = &args[2];
    let signal_file: fs::File = fs::File::open(signal_file_path).expect("Error opening signal CSV file");
    let mut reader = csv::ReaderBuilder::new().trim(csv::Trim::All).has_headers(true).from_reader(signal_file);

    for result in reader.records() {
        if monitor.bz_program_count.max_program_count == 0 {
            internals::debug::debug_print!("Loading in atomics directly!");
            // If no booleanizer instructions present, load CSV file directly as atomics
            let record = &result.expect("Error reading signal values");
            for n in 0..record.len(){
                monitor.atomic_buffer[n] = if record.get(n).expect("Error reading signal values") == "0" {false} else {true};
            }
        } else{
            internals::debug::debug_print!("Loading in signals!");
            // Load values as r2u2_floats (i.e., largest possible option for input signals) into the signal-buffer
            let record = &result.expect("Error reading signal values");
            for n in 0..record.len(){
                monitor.signal_buffer[n] = record.get(n).unwrap().parse::<r2u2_float>().expect("Error reading signal values");
            }
        }
        engines::r2u2_step(&mut monitor);
    }

}

