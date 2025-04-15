import pathlib
import shutil

from c2po import cpt, log, sat, types, options

MODULE_CODE = "SRLZ"


def write_outputs(
    program: cpt.Program,
    context: cpt.Context
) -> None:
    """Writes `program` to each of the given filenames if they are not `None`."""
    if context.options.write_c2po_filename is not None:
        log.debug(MODULE_CODE, 1, f"Writing C2PO to {context.options.write_c2po_filename}")
        with open(context.options.write_c2po_filename, "w") as f:
            f.write(str(program))
    
    if context.options.write_prefix_filename is not None:
        log.debug(MODULE_CODE, 1, f"Writing prefix format to {context.options.write_prefix_filename}")
        with open(context.options.write_prefix_filename, "w") as f:
            f.write(repr(program))

    if context.options.write_mltl_filename is not None:
        log.debug(MODULE_CODE, 1, f"Dumping MLTL standard format to {context.options.write_mltl_filename}")
        with open(context.options.write_mltl_filename, "w") as f:
            f.write(cpt.to_mltl_std(program, context))

    if context.options.write_pickle_filename is not None:
        log.debug(MODULE_CODE, 1, f"Writing pickled program to {context.options.write_pickle_filename}")
        with open(context.options.write_pickle_filename, "wb") as f:
            f.write(program.pickle())

    if context.options.write_smt_dirname is not None:
        log.debug(MODULE_CODE, 1, f"Writing SMT encoding to {context.options.write_smt_dirname}")

        smt_output_path = pathlib.Path(context.options.write_smt_dirname)
        if smt_output_path.is_file():
            smt_output_path.unlink()
        elif smt_output_path.is_dir():
            shutil.rmtree(smt_output_path)
        
        smt_output_path.mkdir()

        for spec in program.ft_spec_set.get_specs():
            if isinstance(spec, cpt.Contract):
                continue
            expr = spec.get_expr()
            with open(str(smt_output_path / f"{spec.symbol}.smt"), "w") as f:
                if context.options.smt_encoding == options.SMTTheories.UFLIA:
                    f.write(sat.to_uflia_smtlib2(expr, context))
                elif context.options.smt_encoding == options.SMTTheories.QF_UFLIA:
                    f.write(sat.to_qfuflia_smtlib2(expr, context))
                elif context.options.smt_encoding == options.SMTTheories.AUFLIA:
                    f.write(sat.to_auflia_smtlib2(expr, context))
                elif context.options.smt_encoding == options.SMTTheories.QF_AUFLIA:
                    f.write(sat.to_qfauflia_smtlib2(expr, context))
                elif context.options.smt_encoding == options.SMTTheories.AUFBV:
                    f.write(sat.to_aufbv_smtlib2(expr, context))
                elif context.options.smt_encoding == options.SMTTheories.QF_AUFBV:
                    f.write(sat.to_qfaufbv_smtlib2(expr, context))
                elif context.options.smt_encoding == options.SMTTheories.QF_BV:
                    f.write(sat.to_qfbv_smtlib2(expr, context, expr.wpd + 1))
                elif context.options.smt_encoding == options.SMTTheories.QF_BV_INCR:
                    log.warning(MODULE_CODE, "qf_bv_incr encoding writes multiple files incrementally depending on SMT results, not writing")
                elif context.options.smt_encoding == options.SMTTheories.QF_BV_LOG:
                    f.write(sat.to_qfbv_log_smtlib2(expr, context, expr.wpd + 1))
                elif context.options.smt_encoding == options.SMTTheories.QF_BV_LOG_INCR:
                    log.warning(MODULE_CODE, "qf_bv_log_incr encoding writes multiple files incrementally depending on SMT results, not writing")

    if context.options.write_bounds_filename is not None:
        write_bounds_path = pathlib.Path(context.options.write_bounds_filename)
        if write_bounds_path.is_file():
            log.warning(MODULE_CODE, f"File {write_bounds_path} already exists. Overwriting.")
        elif write_bounds_path.exists():
            log.warning(MODULE_CODE, f"Path {write_bounds_path} not a file and already exists. Skipping.")
            return
        
        if context.options.impl == types.R2U2Implementation.C:
            log.debug(MODULE_CODE, 1, f"Writing bounds.h to {write_bounds_path}")
            with open(write_bounds_path, "w") as f:
                f.write(program.get_bounds_c_file())
        elif context.options.impl == types.R2U2Implementation.RUST:
            log.debug(MODULE_CODE, 1, f"Writing config.toml to {write_bounds_path}")
            with open(write_bounds_path, "w") as f:
                f.write(program.get_bounds_rs_file())
        else:
            log.warning(MODULE_CODE, f"Unsupported implementation {context.options.impl}, skipping bounds file write")