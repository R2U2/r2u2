from typing import Any
from c2po import cpt, command

def write_c2po(
    program: cpt.Program,
    options: dict[str, Any]
) -> command.ReturnCode:
    """Writes the C2PO representation of the program to the given filename."""
    with open(options["filename"], "w") as f:
        f.write(str(program))
    return command.ReturnCode.SUCCESS

write_c2po_command = command.Command(
    name="write_c2po",
    description="Write the C2PO representation of the program to the given filename.",
    options=[
        {
            "name": "filename",
            "description": "The filename to write the C2PO representation to",
            "required": True,
            "type": str,
            "default": None,
            "choices": None
        },
    ],
    func=lambda program, context, options: write_c2po(program, options),
    guards=[],
)
command.CommandRegistry.register(write_c2po_command)

def write_prefix(
    program: cpt.Program,
    options: dict[str, Any]
) -> command.ReturnCode:
    """Writes the prefix representation of the program to the given filename."""
    with open(options["filename"], "w") as f:
        f.write(repr(program))
    return command.ReturnCode.SUCCESS

write_prefix_command = command.Command(
    name="write_prefix",
    description="Write the prefix representation of the program to the given filename.",
    options=[
        {
            "name": "filename",
            "description": "The filename to write the prefix representation to",
            "required": True,
            "type": str,
            "default": None,
            "choices": None
        },
    ],
    func=lambda program, context, options: write_prefix(program, options),
    guards=[],
)
command.CommandRegistry.register(write_prefix_command)

def write_mltl(
    program: cpt.Program,
    context: cpt.Context,
    options: dict[str, Any]
) -> command.ReturnCode:
    """Writes the MLTL standard representation of the program to the given filename."""
    with open(options["filename"], "w") as f:
        f.write(cpt.to_mltl_std(program, context))
    return command.ReturnCode.SUCCESS

write_mltl_command = command.Command(
    name="write_mltl",
    description="Write the MLTL standard representation of the program to the given filename.",
    options=[
        {
            "name": "filename",
            "description": "The filename to write the MLTL standard representation to",
            "required": True,
            "type": str,
            "default": None,
            "choices": None
        },
    ],
    func=write_mltl,
    guards=[],
)
command.CommandRegistry.register(write_mltl_command)

def write_pickle(
    program: cpt.Program,
    options: dict[str, Any]
) -> command.ReturnCode:
    """Writes the pickle representation of the program to the given filename."""
    with open(options["filename"], "wb") as f:
        f.write(program.pickle())
    return command.ReturnCode.SUCCESS

write_pickle_command = command.Command(
    name="write_pickle",
    description="Write the pickle representation of the program to the given filename.",
    options=[
        {
            "name": "filename",
            "description": "The filename to write the pickle representation to",
            "required": True,
            "type": str,
            "default": None,
            "choices": None
        },
    ],
    func=lambda program, context, options: write_pickle(program, options),
    guards=[],
)
command.CommandRegistry.register(write_pickle_command)
