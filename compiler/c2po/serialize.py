import pathlib
import shutil
from c2po import cpt, log, types

MODULE_CODE = "SRLZ"


def file_setup(path: pathlib.Path) -> bool:
    """ 
    Sets up a file or directory at `path` for writing.
    If the file or directory already exists and is a file, it will be overwritten.
    If the file or directory already exists and is a directory, it will be used as the output directory.
    Returns `True` if the output path is a directory, `False` otherwise.
    """
    output_is_dir = False
    if path.is_file():
        path.unlink()
    elif path.is_dir():
        output_is_dir = True

    return output_is_dir


def write_encoding_map(output_path: pathlib.Path, encoding_map: dict[cpt.Formula, pathlib.Path], output_is_dir: bool) -> None:
    """
    Writes the encoding map to the given output path. 
    If the encoding map has only a single formula, the output path is a file. 
    Otherwise, the output path is a directory.
    The output path is a file if the output_path is a file, otherwise it is a directory.
    """
    log.debug(MODULE_CODE, 1, f"Writing encoding map to {output_path}")

    if len(encoding_map.keys()) == 1:
        smt_encoding_path = list(encoding_map.values())[0] 
        if output_is_dir:
            output_path = output_path / smt_encoding_path.name
        shutil.copy(smt_encoding_path, output_path)
        return

    output_path.mkdir(parents=True, exist_ok=True)
    for _, smt_encoding_path in encoding_map.items():
        filename = smt_encoding_path.name
        shutil.copy(smt_encoding_path, output_path / f"{filename}")


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

    if context.options.write_sat_name is not None:
        log.debug(MODULE_CODE, 1, f"Writing satisfiability SMT encoding to {context.options.write_sat_name}")
        smt_output_path = pathlib.Path(context.options.write_sat_name)
        output_is_dir = file_setup(smt_output_path)
        write_encoding_map(smt_output_path, context.sat_smt_map, output_is_dir)

    if context.options.write_equiv_name is not None:
        log.debug(MODULE_CODE, 1, f"Writing equivalence SMT encoding to {context.options.write_equiv_name}")
        equiv_output_path = pathlib.Path(context.options.write_equiv_name)
        output_is_dir = file_setup(equiv_output_path)
        if output_is_dir:
            shutil.copy(context.equiv_smt_path, equiv_output_path / context.equiv_smt_path.name)
        else:
            shutil.copy(context.equiv_smt_path, equiv_output_path)

    if context.options.write_eqsat_equiv_smt_name is not None:
        log.debug(MODULE_CODE, 1, f"Writing EQSat SMT encoding to {context.options.write_eqsat_equiv_smt_name}")
        eqsat_smt_output_path = pathlib.Path(context.options.write_eqsat_equiv_smt_name)
        output_is_dir = file_setup(eqsat_smt_output_path)
        write_encoding_map(eqsat_smt_output_path, context.eqsat_smt_map, output_is_dir)

    if context.options.write_eqsat_egglog_name is not None:
        log.debug(MODULE_CODE, 1, f"Writing egglog encoding to {context.options.write_eqsat_egglog_name}")
        eqsat_egglog_output_path = pathlib.Path(context.options.write_eqsat_egglog_name)
        output_is_dir = file_setup(eqsat_egglog_output_path)
        write_encoding_map(eqsat_egglog_output_path, context.eqsat_egglog_map, output_is_dir)

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