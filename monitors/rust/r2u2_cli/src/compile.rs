use pyo3::prelude::*;
use pyo3::exceptions::PyTypeError;
use pyo3::ffi::c_str;

pub fn c2po_compile(spec_filename: &str,
    trace_filename: &str,
    map_filename: &str,
    impl_str: &str,
    output_filename: &str,
    write_bounds_filename: &str,
    enable_booleanizer: bool,
    enable_aux: bool,
    enable_rewrite: bool,
    enable_cse: bool,
    enable_sat: bool,
    timeout_sat: i32) {
    // Load all Python module source code
    let c2po_code = c_str!(include_str!("../compiler/c2po/__init__.py"));
    let log_code = c_str!(include_str!("../compiler/c2po/log.py"));
    let types_code = c_str!(include_str!("../compiler/c2po/types.py"));
    let stats_code = c_str!(include_str!("../compiler/c2po/stats.py"));
    let util_code = c_str!(include_str!("../compiler/c2po/util.py"));
    let cpt_code = c_str!(include_str!("../compiler/c2po/cpt.py"));
    let command_code = c_str!(include_str!("../compiler/c2po/command.py"));
    let lex_code = c_str!(include_str!("../compiler/c2po/sly/lex.py"));
    let yacc_code = c_str!(include_str!("../compiler/c2po/sly/yacc.py"));
    let sly_code = c_str!(include_str!("../compiler/c2po/sly/__init__.py"));
    let parse_utils_code = c_str!(include_str!("../compiler/c2po/parse_utils.py"));
    let desugar_code = c_str!(include_str!("../compiler/c2po/desugar.py"));
    let rewrite_code = c_str!(include_str!("../compiler/c2po/rewrite.py"));
    let cse_code = c_str!(include_str!("../compiler/c2po/cse.py"));
    let transform_code = c_str!(include_str!("../compiler/c2po/transform.py"));
    let atomics_code = c_str!(include_str!("../compiler/c2po/atomics.py"));
    let scq_code = c_str!(include_str!("../compiler/c2po/scq.py"));
    let type_check_code = c_str!(include_str!("../compiler/c2po/type_check.py"));
    let assemble_code = c_str!(include_str!("../compiler/c2po/assemble.py"));
    let sat_code = c_str!(include_str!("../compiler/c2po/sat.py"));
    let parse_egglog_output_code = c_str!(include_str!("../compiler/c2po/parse_egglog_output.py"));
    let eqsat_code = c_str!(include_str!("../compiler/c2po/eqsat.py"));
    let serialize_code = c_str!(include_str!("../compiler/c2po/serialize.py"));
    let parse_mltl_code = c_str!(include_str!("../compiler/c2po/parse_mltl.py"));
    let parse_c2po_code = c_str!(include_str!("../compiler/c2po/parse_c2po.py"));
    let parse_equiv_code = c_str!(include_str!("../compiler/c2po/parse_equiv.py"));
    let main_code = c_str!(include_str!("../compiler/c2po/main.py"));

    let from_python = Python::attach(|py| -> PyResult<()> {
        // Import modules in dependency order
        // Base modules (no c2po dependencies)
        PyModule::from_code(py, c2po_code, c_str!("c2po/__init__.py"), c_str!("c2po"))?;
        PyModule::from_code(py, log_code, c_str!("c2po/log.py"), c_str!("c2po.log"))?;
        PyModule::from_code(py, types_code, c_str!("c2po/types.py"), c_str!("c2po.types"))?;
        PyModule::from_code(py, stats_code, c_str!("c2po/stats.py"), c_str!("c2po.stats"))?;
        PyModule::from_code(py, util_code, c_str!("c2po/util.py"), c_str!("c2po.util"))?;
        
        // Modules that depend on base modules
        PyModule::from_code(py, cpt_code, c_str!("c2po/cpt.py"), c_str!("c2po.cpt"))?;
        PyModule::from_code(py, command_code, c_str!("c2po/command.py"), c_str!("c2po.command"))?;
        
        // Sly modules (lexer/parser)
        PyModule::from_code(py, lex_code, c_str!("sly/lex.py"), c_str!("c2po.sly.lex"))?;
        PyModule::from_code(py, yacc_code, c_str!("sly/yacc.py"), c_str!("c2po.sly.yacc"))?;
        PyModule::from_code(py, sly_code, c_str!("sly/__init__.py"), c_str!("c2po.sly"))?;
        
        // Parse modules
        PyModule::from_code(py, parse_utils_code, c_str!("c2po/parse_utils.py"), c_str!("c2po.parse_utils"))?;
        
        // Transform and optimization modules
        PyModule::from_code(py, desugar_code, c_str!("c2po/desugar.py"), c_str!("c2po.desugar"))?;
        PyModule::from_code(py, rewrite_code, c_str!("c2po/rewrite.py"), c_str!("c2po.rewrite"))?;
        PyModule::from_code(py, cse_code, c_str!("c2po/cse.py"), c_str!("c2po.cse"))?;
        PyModule::from_code(py, transform_code, c_str!("c2po/transform.py"), c_str!("c2po.transform"))?;
        PyModule::from_code(py, atomics_code, c_str!("c2po/atomics.py"), c_str!("c2po.atomics"))?;
        PyModule::from_code(py, scq_code, c_str!("c2po/scq.py"), c_str!("c2po.scq"))?;
        PyModule::from_code(py, type_check_code, c_str!("c2po/type_check.py"), c_str!("c2po.type_check"))?;
        PyModule::from_code(py, assemble_code, c_str!("c2po/assemble.py"), c_str!("c2po.assemble"))?;
        PyModule::from_code(py, sat_code, c_str!("c2po/sat.py"), c_str!("c2po.sat"))?;
        PyModule::from_code(py, parse_egglog_output_code, c_str!("c2po/parse_egglog_output.py"), c_str!("c2po.parse_egglog_output"))?;
        PyModule::from_code(py, eqsat_code, c_str!("c2po/eqsat.py"), c_str!("c2po.eqsat"))?;
        PyModule::from_code(py, serialize_code, c_str!("c2po/serialize.py"), c_str!("c2po.serialize"))?;
        PyModule::from_code(py, parse_mltl_code, c_str!("c2po/parse_mltl.py"), c_str!("c2po.parse_mltl"))?;
        PyModule::from_code(py, parse_c2po_code, c_str!("c2po/parse_c2po.py"), c_str!("c2po.parse_c2po"))?;
        PyModule::from_code(py, parse_equiv_code, c_str!("c2po/parse_equiv.py"), c_str!("c2po.parse_equiv"))?;
        
        // Main module (depends on all others)
        let main_py = PyModule::from_code(py, main_code, c_str!("c2po/main.py"), c_str!("c2po.main"))?;
        
        // Call main_rs function
        let args = (
            spec_filename,
            trace_filename,
            map_filename,
            impl_str,
            output_filename,
            write_bounds_filename,
            enable_booleanizer,
            enable_aux,
            enable_rewrite,
            enable_cse,
            enable_sat,
            timeout_sat,
        );
        let result: Bound<'_, PyAny> = main_py.getattr("main_rs")?.call1(args)?;
        
        // Get ReturnCode enum and compare properly
        let command_module = py.import("c2po.command")?;
        let return_code_success = command_module.getattr("ReturnCode")?.getattr("SUCCESS")?;
        
        // Compare the result with ReturnCode.SUCCESS using eq for enum comparison
        if result.eq(&return_code_success)? {
            Ok(())
        } else {
            Err(PyTypeError::new_err(format!("Compilation failed with return code: {}", result.to_string())))
        }
    });
    if from_python.is_err(){
        println!("from_python: {:?}", from_python);
        println!("Compilation failed!");
        std::process::exit(1);
    }
}