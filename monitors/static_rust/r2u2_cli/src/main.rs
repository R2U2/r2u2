use std::env;
use std::fs;
use csv::{Reader, StringRecord};
use r2u2_core;

fn main() {
    println!("HERE!");
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

    let mut monitor = r2u2_core::Monitor::default();
    r2u2_core::process_binary_file(&spec_file, &mut monitor);

    let signal_file_path = &args[2];
    let signal_file: fs::File = fs::File::open(signal_file_path).expect("Error opening signal CSV file");
    let mut reader = csv::ReaderBuilder::new().trim(csv::Trim::All).has_headers(true).from_reader(signal_file);
    
    for result in reader.records() {
        let record = &result.expect("Error reading signal values");
        for n in 0..record.len(){
            r2u2_core::load_string_signal(&mut monitor, n, record.get(n).expect("Error reading signal values"));
        }
        r2u2_core::r2u2_step(&mut monitor);
    }

}

