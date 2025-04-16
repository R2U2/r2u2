use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::ffi::OsStr;
use clap::{Parser, Subcommand};

mod compile;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    
}

#[derive(Subcommand)]
enum Commands {
    /// Compiles .c2po or .mltl file to spec.bin for R2U2
    // Compile {
    //     /// Sets a specification .c2po or .mltl file
    //     #[arg(value_parser = valid_spec_file)]
    //     spec: PathBuf,

    //     /// Sets a trace .csv or a map .map file
    //     #[arg(value_parser = valid_map_file)]
    //     map: PathBuf,

    //     /// Sets location to save spec.bin file (default = current directory)
    //     #[arg(short,long, value_name = "PATH", value_parser=valid_location)]
    //     output: Option<PathBuf>,

    //     /// Disables booleanizer (default = booleanizer enabled)
    //     #[arg(long,default_value_t=false)]
    //     disable_booleanizer: bool,

    //     /// Disable Assume-Guarantee Contract (AGC) and auxiliary specification logging
    //     #[arg(long,default_value_t=false)]
    //     disable_aux: bool,

    //     /// Disables rewrite rules (default = rewrite rules enabled)
    //     #[arg(long,default_value_t=false)]
    //     disable_rewrite: bool,

    //     /// Disables common subexpression elimination (CSE) (default = CSE enabled)
    //     #[arg(long,default_value_t=false)]
    //     disable_cse: bool,

    //     /// Enables SAT checking through Z3 -> Z3 must be installed (default = SAT disabled)
    //     #[arg(long,default_value_t=false)]
    //     enable_sat: bool,

    //     /// Set the timeout of SAT calls in seconds (default: 3600)
    //     #[arg(long)]
    //     timeout_sat: Option<i32>,
    // },

    /// Runs R2U2 over a trace.csv file
    Run {
        /// Sets a specification .c2po or .mltl file or spec.bin
        #[arg(value_parser = valid_spec_input_file)]
        spec: PathBuf,

        /// Sets a trace .csv file
        #[arg(value_parser = valid_trace_file)]
        trace: PathBuf,

        /// Sets location to save output in a file (default = print to terminal)
        #[arg(short, long, value_name = "PATH", value_parser=valid_location)]
        output: Option<PathBuf>,

        /// Disable assume-guarantee contract status logging
        #[arg(long,default_value_t=false)]
        disable_contracts: bool,

        /// Enable auxiliary specification logging
        #[arg(long,default_value_t=false)]
        enable_aux: bool,
    },
}

fn valid_spec_input_file(s: &str) -> Result<PathBuf, String> {
    let file : PathBuf = s
        .parse()
        .map_err(|_| format!("`{s}` isn't a file"))?;
    if !file.exists() {
        return Err(format!(
            "{} is not valid file",file.to_string_lossy()
        ))
    }
    if file.extension().and_then(OsStr::to_str) == Some("c2po") || 
    file.extension().and_then(OsStr::to_str) == Some("mltl") ||
    file.extension().and_then(OsStr::to_str) == Some("bin"){
        Ok(file as PathBuf)
    } else {
        Err(format!(
            "{} is not a .c2po, .mltl, or spec.bin file",file.extension().and_then(OsStr::to_str).unwrap()
        ))
    }
}

// fn valid_spec_file(s: &str) -> Result<PathBuf, String> {
//     let file : PathBuf = s
//         .parse()
//         .map_err(|_| format!("`{s}` isn't a file"))?;
//     if !file.exists() {
//         return Err(format!(
//             "{} is not valid file",file.to_string_lossy()
//         ))
//     }
//     if file.extension().and_then(OsStr::to_str) == Some("c2po") || 
//     file.extension().and_then(OsStr::to_str) == Some("mltl") {
//         Ok(file as PathBuf)
//     } else {
//         Err(format!(
//             "{s} is not a .c2po or .mltl file"
//         ))
//     }
// }

fn valid_trace_file(s: &str) -> Result<PathBuf, String> {
    let file : PathBuf = s
        .parse()
        .map_err(|_| format!("`{s}` isn't a file"))?;
    if !file.exists() {
        return Err(format!(
            "{} is not valid file",file.to_string_lossy()
        ))
    }
    if file.extension().and_then(OsStr::to_str) == Some("csv"){
        Ok(file as PathBuf)
    } else {
        Err(format!(
            "{} is not a .csv file", file.extension().and_then(OsStr::to_str).unwrap()
        ))
    }
}

// fn valid_map_file(s: &str) -> Result<PathBuf, String> {
//     let file : PathBuf = s
//         .parse()
//         .map_err(|_| format!("`{s}` isn't a file"))?;
//     if !file.exists() {
//         return Err(format!(
//             "{} is not valid file",file.to_string_lossy()
//         ))
//     }
//     if file.extension().and_then(OsStr::to_str) == Some("csv") || 
//     file.extension().and_then(OsStr::to_str) == Some("map"){
//         Ok(file as PathBuf)
//     } else {
//         Err(format!(
//             "{s} is not a .csv or .map file"
//         ))
//     }
// }

fn valid_location(s: &str) -> Result<PathBuf, String> {
    let path : PathBuf = s
        .parse()
        .map_err(|_| format!("`{s}` isn't a path"))?;
    if path.exists() {
        Ok(path as PathBuf)
    } else {
        Err(format!(
            "{} is not valid location",path.to_string_lossy()
        ))
    }
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Some(Commands::Run { spec, trace, output, disable_contracts, enable_aux}) => {
            let spec_file: Vec<u8>;
            // if spec.extension().and_then(OsStr::to_str) == Some("c2po") || 
            //     spec.extension().and_then(OsStr::to_str) == Some("mltl") {
            //     let random_file = srfng::Generator::new().generate().as_str().to_owned();
            //     compile::c2po_compile(spec.to_str().unwrap(),
            //         trace.to_str().unwrap(),
            //         "",
            //         &random_file,
            //         true,
            //         *enable_aux || !disable_contracts,
            //         true,
            //         true,
            //         false,
            //         3600,
            //         );
            //     let new_spec = PathBuf::from("./".to_owned() + &random_file);
            //     spec_file = fs::read(new_spec).expect("Error opening specification file");
            //     let _ = fs::remove_file("./".to_owned() + &random_file);
            // } else {
            //     spec_file = fs::read(spec).expect("Error opening specification file");
            // }

            spec_file = fs::read(spec).expect("Error opening specification file");
            let mut monitor = r2u2_core::get_monitor(&spec_file);

            let signal_file: fs::File = fs::File::open(trace).expect("Error opening signal CSV file");
            let mut reader = csv::ReaderBuilder::new().trim(csv::Trim::All).has_headers(false).comment(Some(b'#')).from_reader(signal_file);

            if output.is_some(){
                let mut out_location = output.clone().unwrap();
                out_location.push("r2u2_out.log");
                let mut output_file: fs::File = fs::File::create(out_location).expect("Error creating output file");
                for result in reader.records() {
                    let record = &result.expect("Error reading signal values");
                    let first_element = record.get(0).expect("Error reading signal values");
                    if first_element.starts_with('@') {
                        let end_idx = first_element.find(" ").unwrap_or(1);
                        match first_element[1..end_idx].parse::<u32>() {
                            Ok(n) => { monitor.time_stamp = n; }
                            Err(_e) => {}
                        }
                        r2u2_core::load_string_signal(&mut monitor, 0, &first_element[end_idx+1..first_element.len()]);
                    } else {
                        r2u2_core::load_string_signal(&mut monitor, 0, record.get(0).expect("Error reading signal values"));
                    }
                    for n in 1..record.len(){
                        r2u2_core::load_string_signal(&mut monitor, n, record.get(n).expect("Error reading signal values"));
                    }
                    if r2u2_core::monitor_step(&mut monitor) {
                        if *enable_aux {
                            for out in r2u2_core::get_output_buffer(&monitor) {
                                let _ = output_file.write_fmt(format_args!("{} ({}):{},{}\n", out.spec_str, out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"}));
                            }
                        } else {
                            for out in r2u2_core::get_output_buffer(&monitor) {
                                let _ = output_file.write_fmt(format_args!("{}:{},{}\n", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"}));
                            }
                        }
                        if !disable_contracts {
                            for out in r2u2_core::get_contract_buffer(&monitor) {
                                let _ = output_file.write_fmt(format_args!("Contract {} {} at {}\n", out.spec_str, if out.status == r2u2_core::AGC_VERIFIED {"verified"} else if out.status == r2u2_core::AGC_INVALID {"invalid"} else {"inactive"}, out.time));
                            }
                        }
                    } else {
                        let _ = output_file.write_fmt(format_args!("Overflow occurred!!!!\n"));
                    }
                }
                println!("Output written to {}/r2u2_out.log", output.clone().unwrap().to_string_lossy());
            } else{
                for result in reader.records() {
                    let record = &result.expect("Error reading signal values");
                    let first_element = record.get(0).expect("Error reading signal values");
                    if first_element.starts_with('@') {
                        let end_idx = first_element.find(" ").unwrap_or(1);
                        match first_element[1..end_idx].parse::<u32>() {
                            Ok(n) => { monitor.time_stamp = n; }
                            Err(_e) => {}
                        }
                        r2u2_core::load_string_signal(&mut monitor, 0, &first_element[end_idx+1..first_element.len()]);
                    } else {
                        r2u2_core::load_string_signal(&mut monitor, 0, record.get(0).expect("Error reading signal values"));
                    }
                    for n in 1..record.len(){
                        r2u2_core::load_string_signal(&mut monitor, n, record.get(n).expect("Error reading signal values"));
                    }
                    if r2u2_core::monitor_step(&mut monitor) {
                        if *enable_aux {
                            for out in r2u2_core::get_output_buffer(&monitor) {
                                println!("{} ({}):{},{}", out.spec_str, out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
                            }
                        } else {
                            for out in r2u2_core::get_output_buffer(&monitor) {
                                println!("{}:{},{}", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
                            }
                        }
                        if !disable_contracts {
                            for out in r2u2_core::get_contract_buffer(&monitor) {
                                println!("Contract {} {} at {}", out.spec_str, if out.status == r2u2_core::AGC_VERIFIED {"verified"} else if out.status == r2u2_core::AGC_INVALID {"invalid"} else {"inactive"}, out.time);
                            }
                        }
                    } else {
                        println!("Overflow occurred!!!!")
                    }
                }
            }
        },
        // Some(Commands::Compile { spec, map, output,  disable_booleanizer, 
        //     disable_aux, disable_rewrite, disable_cse, enable_sat, timeout_sat}) => {
        //     let mut out_location: String;
        //     if output.is_some(){
        //         out_location = output.clone().unwrap_or_else(PathBuf::new).to_str().unwrap_or(".").to_owned();
        //         out_location.push_str("/spec.bin");
        //     } else{
        //         out_location = "spec.bin".to_owned();
        //     }
        //     compile::c2po_compile(spec.to_str().unwrap(),
        //         if map.extension().and_then(OsStr::to_str) == Some("csv") { map.to_str().unwrap() } else {""},
        //         if map.extension().and_then(OsStr::to_str) == Some("map") { map.to_str().unwrap() } else {""},
        //         &out_location,
        //         !disable_booleanizer,
        //         !disable_aux,
        //         !disable_rewrite,
        //         !disable_cse,
        //         enable_sat.to_owned(),
        //         if timeout_sat.is_some() {timeout_sat.unwrap()} else {3600},
        //         );
        //         println!("Compiling");
        //     }
        _ => {}
    }

}

