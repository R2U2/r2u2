import pathlib
import shutil

from c2po import cpt, log, sat

MODULE_CODE = "SRLZ"

def write_c2po(
    program: cpt.Program,
    input_path: pathlib.Path,
    output_filename: str,
) -> None:
    """Writes string interpretation of `program` to `output_filename` if not '.'"""
    if output_filename == ".":
        return

    output_path = (
        pathlib.Path(output_filename)
        if output_filename != ""
        else input_path.with_suffix(".out.c2po")
    )

    log.debug(MODULE_CODE, 1, f"Writing prefix format to {output_path}")

    with open(output_path, "w") as f:
        f.write(str(program))


def write_prefix(
    program: cpt.Program,
    input_path: pathlib.Path,
    output_filename: str,
) -> None:
    """Writes prefix-notation interpretation of `program` to `output_filename` if not '.'"""
    if output_filename == ".":
        return

    output_path = (
        pathlib.Path(output_filename)
        if output_filename != ""
        else input_path.with_suffix(".prefix.c2po")
    )

    log.debug(MODULE_CODE, 1, f"Writing prefix format to {output_path}")

    with open(output_path, "w") as f:
        f.write(repr(program))


def write_mltl(
    program: cpt.Program,
    context: cpt.Context,
    input_path: pathlib.Path,
    output_filename: str,
) -> None:
    """Writes MLTL standard to `output_filename` if not '.'"""
    if output_filename == ".":
        return

    output_path = (
        pathlib.Path(output_filename)
        if output_filename != ""
        else input_path.with_suffix(".mltl")
    )

    log.debug(MODULE_CODE, 1, f"Dumping MLTL standard format to {output_path}")

    with open(output_path, "w") as f:
        f.write(cpt.to_mltl_std(program, context))


def write_pickle(
    program: cpt.Program,
    input_path: pathlib.Path,
    output_filename: str,
) -> None:
    """Writes pickled `program` to `output_filename` if not '.'"""
    if output_filename == ".":
        return

    output_path = (
        pathlib.Path(output_filename)
        if output_filename != ""
        else input_path.with_suffix(".pickle")
    )

    log.debug(MODULE_CODE, 1, f"Writing pickled program to {output_path}")

    pickled_program = program.pickle()

    with open(output_path, "wb") as f:
        f.write(pickled_program)


def write_smt(
    program: cpt.Program,
    context: cpt.Context,
    input_path: pathlib.Path,
    output_filename: str,
) -> None:
    """Writes smt interpretation of `program` to `output_filename` if not '.'"""
    if output_filename == ".":
        return

    output_path = (
        pathlib.Path(output_filename)
        if output_filename != ""
        else input_path.with_suffix(".smt")
    )

    log.debug(MODULE_CODE, 1, f"Writing SMT encoding to {output_path}")

    if output_path.is_file():
        output_path.unlink()
    elif output_path.is_dir():
        shutil.rmtree(output_path)
    
    output_path.mkdir()

    for spec in program.ft_spec_set.get_specs():
        if isinstance(spec, cpt.Contract):
            continue

        expr = spec.get_expr()

        with open(str(output_path / f"{spec.symbol}.smt"), "w") as f:
            f.write(sat.to_smt_sat_query(expr, context))


def write_outputs(
    program: cpt.Program,
    context: cpt.Context,
    input_path: pathlib.Path,
    write_c2po_filename: str,
    write_prefix_filename: str,
    write_mltl_filename: str,
    write_pickle_filename: str,
    write_smt_dir: str,
) -> None:
    """Writes `program` to each of the given filenames if they are not '.'"""
    write_c2po(program, input_path, write_c2po_filename)
    write_prefix(program, input_path, write_prefix_filename)
    write_mltl(program, context, input_path, write_mltl_filename)
    write_pickle(program, input_path, write_pickle_filename)
    write_smt(program, context, input_path, write_smt_dir)
