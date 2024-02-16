import pathlib

from c2po import cpt, log

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

    log.debug(f"Writing prefix format to {output_path}", MODULE_CODE)

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

    log.debug(f"Writing prefix format to {output_path}", MODULE_CODE)

    with open(output_path, "w") as f:
        f.write(repr(program))


def write_mltl(
    program: cpt.Program,
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

    log.debug(f"Dumping MLTL standard format to {output_path}", MODULE_CODE)

    with open(output_path, "w") as f:
        f.write(cpt.to_mltl_std(program))


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

    log.debug(f"Writing pickled program to {output_path}", MODULE_CODE)

    pickled_program = program.pickle()

    with open(output_path, "wb") as f:
        f.write(pickled_program)


def write_outputs(
    program: cpt.Program,
    input_path: pathlib.Path,
    write_c2po_filename: str,
    write_prefix_filename: str,
    write_mltl_filename: str,
    write_pickle_filename: str,
) -> None:
    """Writes `program` to each of the given filenames if they are not '.'"""
    write_c2po(program, input_path, write_c2po_filename)
    write_prefix(program, input_path, write_prefix_filename)
    write_mltl(program, input_path, write_mltl_filename)
    write_pickle(program, input_path, write_pickle_filename)
