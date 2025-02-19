import pathlib
import shutil

from c2po import cpt, log, sat, options

MODULE_CODE = "SRLZ"


def write_outputs(
    program: cpt.Program,
    context: cpt.Context
) -> None:
    """Writes `program` to each of the given filenames if they are not '.'"""
    if options.write_c2po:
        log.debug(MODULE_CODE, 1, f"Writing C2PO to {options.write_c2po_filename}")
        with open(options.write_c2po_filename, "w") as f:
            f.write(str(program))
    
    if options.write_prefix:
        log.debug(MODULE_CODE, 1, f"Writing prefix format to {options.write_prefix_filename}")
        with open(options.write_prefix_filename, "w") as f:
            f.write(repr(program))

    if options.write_mltl:
        log.debug(MODULE_CODE, 1, f"Dumping MLTL standard format to {options.write_mltl_filename}")
        with open(options.write_mltl_filename, "w") as f:
            f.write(cpt.to_mltl_std(program, context))

    if options.write_pickle:
        log.debug(MODULE_CODE, 1, f"Writing pickled program to {options.write_pickle_filename}")
        with open(options.write_pickle_filename, "wb") as f:
            f.write(program.pickle())

    if options.write_smt:
        log.debug(MODULE_CODE, 1, f"Writing SMT encoding to {options.write_smt_dirname}")

        smt_output_path = pathlib.Path(options.write_smt_dirname)
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
                if options.smt_encoding == options.SMTTheories.UFLIA:
                    f.write(sat.to_uflia_smtlib2(expr, context))
                elif options.smt_encoding == options.SMTTheories.AUFLIA:
                    f.write(sat.to_auflia_smtlib2(expr, context))
                elif options.smt_encoding == options.SMTTheories.QF_AUFLIA:
                    f.write(sat.to_qfaufbv_smtlib2(expr, context))
                elif options.smt_encoding == options.SMTTheories.AUFBV:
                    f.write(sat.to_aufbv_smtlib2(expr, context))
                elif options.smt_encoding == options.SMTTheories.QF_AUFBV:
                    f.write(sat.to_qfaufbv_smtlib2(expr, context))
                elif options.smt_encoding == options.SMTTheories.QF_BV:
                    f.write(sat.to_qfbv_smtlib2(expr, context, expr.wpd + 1))
                elif options.smt_encoding == options.SMTTheories.QF_BV_INCR:
                    log.warning(MODULE_CODE, "qf_bv_incr encoding writes multiple files incrementally depending on SMT results, not writing")
