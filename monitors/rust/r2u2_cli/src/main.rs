use r2u2_core;

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::ffi::OsStr;
use clap::{Parser, Subcommand};
use pyo3::prelude::*;
use pyo3::exceptions::PyTypeError;
use pyo3::ffi::c_str;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    
}

#[derive(Subcommand)]
enum Commands {
    /// Compiles .c2po or .mltl file to spec.bin for R2U2
    Compile {
        /// Sets a specification .c2po or .mltl file
        #[arg(value_parser = valid_spec_file)]
        spec: PathBuf,

        /// Sets a trace .csv or a map .map file
        #[arg(value_parser = valid_map_file)]
        map: PathBuf,

        /// Sets location to save spec.bin file (default = current directory)
        #[arg(short,long, value_name = "PATH", value_parser=valid_location)]
        output: Option<PathBuf>,

        /// Enables booleanizer (default = booleanizer enabled)
        #[arg(long,default_value_t=false)]
        disable_booleanizer: bool,

        /// Enables rewrite rules (default = rewrite rules enabled)
        #[arg(long,default_value_t=false)]
        disable_rewrite: bool,

        /// Enables common subexpression elimination (CSE) (default = CSE enabled)
        #[arg(long,default_value_t=false)]
        disable_cse: bool,

        /// Enables SAT checking through Z3 -> Z3 must be installed (default = SAT disabled)
        #[arg(long,default_value_t=false)]
        enable_sat: bool,

        /// Set the timeout of SAT calls in seconds (default: 3600)
        #[arg(long)]
        timeout_sat: Option<i32>,
    },

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

        /// Disable auxiliary data output (e.g., assume-guarantee contract status)
        #[arg(long,default_value_t=false)]
        disable_aux: bool,
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

fn valid_spec_file(s: &str) -> Result<PathBuf, String> {
    let file : PathBuf = s
        .parse()
        .map_err(|_| format!("`{s}` isn't a file"))?;
    if !file.exists() {
        return Err(format!(
            "{} is not valid file",file.to_string_lossy()
        ))
    }
    if file.extension().and_then(OsStr::to_str) == Some("c2po") || 
    file.extension().and_then(OsStr::to_str) == Some("mltl") {
        Ok(file as PathBuf)
    } else {
        Err(format!(
            "{} is not a .c2po or .mltl file", s
        ))
    }
}

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

fn valid_map_file(s: &str) -> Result<PathBuf, String> {
    let file : PathBuf = s
        .parse()
        .map_err(|_| format!("`{s}` isn't a file"))?;
    if !file.exists() {
        return Err(format!(
            "{} is not valid file",file.to_string_lossy()
        ))
    }
    if file.extension().and_then(OsStr::to_str) == Some("csv") || 
    file.extension().and_then(OsStr::to_str) == Some("map"){
        Ok(file as PathBuf)
    } else {
        Err(format!(
            "{} is not a .csv or .map file", s
        ))
    }
}

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
        Some(Commands::Run { spec, trace, output , disable_aux}) => {
            let spec_file: Vec<u8>;
            if spec.extension().and_then(OsStr::to_str) == Some("c2po") || 
                spec.extension().and_then(OsStr::to_str) == Some("mltl") {
                let random_file = srfng::Generator::new().generate().as_str().to_owned();
                c2po_compile(spec.to_str().unwrap(),
                    trace.to_str().unwrap(),
                    "",
                    &random_file,
                    true,
                    true,
                    true,
                    false,
                    3600,
                    );
                let new_spec = PathBuf::from("./".to_owned() + &random_file);
                spec_file = fs::read(new_spec).expect("Error opening specification file");
                let _ = fs::remove_file("./".to_owned() + &random_file);
            } else {
                spec_file = fs::read(spec).expect("Error opening specification file");
            }

            let mut monitor = r2u2_core::get_monitor(&spec_file);

            let signal_file: fs::File = fs::File::open(trace).expect("Error opening signal CSV file");
            let mut reader = csv::ReaderBuilder::new().trim(csv::Trim::All).has_headers(true).from_reader(signal_file);
            
            if output.is_some(){
                let mut out_location = output.clone().unwrap();
                out_location.push("r2u2_out.log");
                let mut output_file: fs::File = fs::File::create(out_location).expect("Error creating output file");
                for result in reader.records() {
                    let record = &result.expect("Error reading signal values");
                    for n in 0..record.len(){
                        r2u2_core::load_string_signal(&mut monitor, n, record.get(n).expect("Error reading signal values"));
                    }
                    if r2u2_core::monitor_step(&mut monitor) {
                        if !disable_aux {
                            for out in r2u2_core::get_output_buffer(&mut monitor).iter() {
                                let _ = output_file.write_fmt(format_args!("{} ({}):{},{}\n", out.spec_str, out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"}));
                            }
                            for out in r2u2_core::get_contract_buffer(&mut monitor).iter() {
                                let _ = output_file.write_fmt(format_args!("Contract {} {} at {}\n", out.spec_str, if out.status == r2u2_core::AGC_VERIFIED {"verified"} else if out.status == r2u2_core::AGC_INVALID {"invalid"} else {"inactive"}, out.time));
                            }
                        } else {
                            for out in r2u2_core::get_output_buffer(&mut monitor).iter() {
                                let _ = output_file.write_fmt(format_args!("{}:{},{}\n", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"}));
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
                    for n in 0..record.len(){
                        r2u2_core::load_string_signal(&mut monitor, n, record.get(n).expect("Error reading signal values"));
                    }
                    if r2u2_core::monitor_step(&mut monitor) {
                        if !disable_aux {
                            for out in r2u2_core::get_output_buffer(&mut monitor).iter() {
                                println!("{} ({}):{},{}", out.spec_str, out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
                            }
                            for out in r2u2_core::get_contract_buffer(&mut monitor).iter() {
                                println!("Contract {} {} at {}", out.spec_str, if out.status == r2u2_core::AGC_VERIFIED {"verified"} else if out.status == r2u2_core::AGC_INVALID {"invalid"} else {"inactive"}, out.time);
                            }
                        } else {
                            for out in r2u2_core::get_output_buffer(&mut monitor).iter() {
                                println!("{}:{},{}", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
                            }
                        }
                    } else {
                        println!("Overflow occurred!!!!")
                    }
                }
            }
        },
        Some(Commands::Compile { spec, map, output,  disable_booleanizer, 
            disable_rewrite, disable_cse, enable_sat, timeout_sat}) => {
            let mut out_location: String;
            if output.is_some(){
                out_location = output.clone().unwrap_or(PathBuf::new()).to_str().unwrap_or(".").to_owned();
                out_location.push_str("/spec.bin");
            } else{
                out_location = "spec.bin".to_owned();
            }
            if map.extension().and_then(OsStr::to_str) == Some("csv") {
                c2po_compile(spec.to_str().unwrap(),
                        map.to_str().unwrap(),
                        "",
                        &out_location,
                        !disable_booleanizer,
                        !disable_rewrite,
                        !disable_cse,
                        enable_sat.to_owned(),
                        if timeout_sat.is_some() {timeout_sat.unwrap()} else {3600},
                        );
            } else if map.extension().and_then(OsStr::to_str) == Some("map") {
                c2po_compile(spec.to_str().unwrap(),
                "",
                map.to_str().unwrap(),
                &out_location,
                !disable_booleanizer,
                !disable_rewrite,
                !disable_cse,
                enable_sat.to_owned(),
                if timeout_sat.is_some() {timeout_sat.unwrap()} else {3600},
                );
            }
        }
        _ => {}
    }

}

fn c2po_compile(input_filename: &str,
    trace_filename: &str,
    map_filename: &str,
    output_filename: &str,
    enable_booleanizer: bool,
    enable_rewrite: bool,
    enable_cse: bool,
    enable_sat: bool,
    timeout_sat: i32) {
    let c2po_code = c_str!(include_str!("../compiler/c2po/__init__.py"));
    let sly_code = c_str!(include_str!("../compiler/c2po/sly/__init__.py"));
    let lex_code = c_str!(include_str!("../compiler/c2po/sly/lex.py"));
    let yacc_code = c_str!(include_str!("../compiler/c2po/sly/yacc.py"));
    let main_code = c_str!(include_str!("../compiler/c2po/main.py"));
    let assemble_code = c_str!(include_str!("../compiler/c2po/assemble.py"));
    let cpt_code= c_str!(include_str!("../compiler/c2po/cpt.py"));
    let eqsat_code= c_str!(include_str!("../compiler/c2po/eqsat.py"));
    let log_code= c_str!(include_str!("../compiler/c2po/log.py"));
    let parse_code= c_str!(include_str!("../compiler/c2po/parse.py"));
    let passes_code = c_str!(include_str!("../compiler/c2po/passes.py"));
    let sat_code = c_str!(include_str!("../compiler/c2po/sat.py"));
    let serialize_code = c_str!(include_str!("../compiler/c2po/serialize.py"));
    let type_check_code = c_str!(include_str!("../compiler/c2po/type_check.py"));
    let types_code = c_str!(include_str!("../compiler/c2po/types.py"));
    let util_code = c_str!(include_str!("../compiler/c2po/util.py"));
    

    let from_python  = Python::with_gil(|py| -> PyResult<()>{
        PyModule::from_code(py, c2po_code, c_str!("c2po/__init__.py"), c_str!("c2po"))?;
        PyModule::from_code(py, log_code, c_str!("c2po/log.py"), c_str!("c2po.log"))?;
        PyModule::from_code(py, types_code, c_str!("c2po/types.py"), c_str!("c2po.types"))?;
        PyModule::from_code(py, cpt_code, c_str!("c2po/cpt.py"), c_str!("c2po.cpt"))?;
        PyModule::from_code(py, assemble_code, c_str!("c2po/assemble.py"), c_str!("c2po.assemble"))?;
        PyModule::from_code(py, lex_code, c_str!("sly/lex.py"), c_str!("c2po.sly.lex"))?;
        PyModule::from_code(py, yacc_code, c_str!("sly//yacc.py"), c_str!("c2po.sly.yacc"))?;
        PyModule::from_code(py, sly_code, c_str!("sly/__init__.py"), c_str!("c2po.sly"))?;
        PyModule::from_code(py, parse_code, c_str!("c2po/parse.py"), c_str!("c2po.parse"))?;
        PyModule::from_code(py, type_check_code, c_str!("c2po/type_check.py"), c_str!("c2po.type_check"))?;
        PyModule::from_code(py, util_code, c_str!("c2po/util.py"), c_str!("c2po.util"))?;
        PyModule::from_code(py, sat_code, c_str!("c2po/sat.py"), c_str!("c2po.sat"))?;
        PyModule::from_code(py, eqsat_code, c_str!("c2po/eqsat.py"), c_str!("c2po.eqsat"))?;
        PyModule::from_code(py, passes_code, c_str!("c2po/passes.py"), c_str!("c2po.passes"))?;
        PyModule::from_code(py, serialize_code, c_str!("c2po/serialize.py"), c_str!("c2po.serialize"))?;
        let main_py = PyModule::from_code(py, main_code, c_str!("c2po/main.py"), c_str!("c2po.main"))?;
        let args = (input_filename,
            trace_filename,
            map_filename,
            output_filename,
            enable_booleanizer,
            enable_rewrite,
            enable_cse,
            enable_sat,
            timeout_sat,
        );
        let result: Bound<'_, PyAny> = main_py.getattr("main")?.call1(args)?;
        let result_str = result.to_string();
        if result_str != "ReturnCode.SUCCESS" {
            println!("Compilation failed!");
            Err(PyTypeError::new_err("Compilation failed!"))
        } else {
            Ok(())
        }
    });
    if from_python.is_err(){
        std::process::exit(0);
    }
}

