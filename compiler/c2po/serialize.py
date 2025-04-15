import pathlib
import shutil

from c2po import cpt, log, sat

MODULE_CODE = "SRLZ"


def write_outputs(
    program: cpt.Program,
    context: cpt.Context
) -> None:
    """Writes `program` to each of the given filenames if they are not '.'"""
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
                f.write(sat.to_uflia_sat_query(expr, context))
