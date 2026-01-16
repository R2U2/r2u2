"""Wrapper functions for the c2po compiler to capture print output and return it
as a string. Used primarily for the playground."""
import sys
import io
from c2po import main

def capture_print_output(func):
    def wrapper(*args, **kwargs):
        captured_output = io.StringIO()
        sys.stdout = captured_output
        sys.stderr = captured_output
        result = func(*args, **kwargs)
        sys.stdout = sys.__stdout__
        sys.stderr = sys.__stderr__
        return (result, captured_output.getvalue())
    return wrapper

def compile_and_log(
    spec_filename: str,
    trace_filename: str = "",
    map_filename: str = "",
    impl_str: str = "",
    output_filename: str = "spec.bin",
    write_bounds_filename: str = "",
    enable_booleanizer: bool = False,
    enable_aux: bool = False,
    enable_rewrite: bool = False,
    enable_cse: bool = False,
    enable_sat: bool = False,
    timeout_sat: int = 3600,
):
    temp = capture_print_output(main.main_rs)
    return temp(
        spec_filename=spec_filename,
        trace_filename=trace_filename,
        map_filename=map_filename,
        impl_str=impl_str,
        output_filename=output_filename,
        write_bounds_filename=write_bounds_filename,
        enable_booleanizer = enable_booleanizer,
        enable_aux = enable_aux,
        enable_rewrite = enable_rewrite,
        enable_cse = enable_cse,
        enable_sat = enable_sat,
        timeout_sat = timeout_sat)
