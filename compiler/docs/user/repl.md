# REPL and Script Mode

C2PO has an interactive command shell (REPL) and a script mode that executes the same commands from
a file. Both modes use the command system documented in [commands](./commands.md), including command
arguments and `--help` on each command. 

## Starting the REPL

Run:

    python3 c2po.py --interactive

The prompt is `c2po>`. Internally, the REPL keeps a current `program` and `context`, and each command
updates that state (for example, `parse_c2po` loads a program, and `type_check` annotates it).

If `~/.c2porc` exists, C2PO executes it before starting the prompt. This is useful for startup defaults
such as debug/logging configuration.

## Core REPL Capabilities

- Run any registered C2PO command (e.g., `help`, `parse_c2po`, `type_check`, `compile`, `assemble`)
- Use normal command options and flags (e.g., `assemble --print out.bin`)
- Get command-specific help (e.g., `compile --help`)
- Save/restore state with `push` and `pop`
- Exit with `exit` (or Ctrl-D / `quit` from the interactive console)

If a command cannot run because prerequisites are missing (guard conditions), C2PO prints an error and
suggests commands that can satisfy the missing condition.

## Script Files

Run a script file with:

    python3 c2po.py --script path/to/pipeline.c2posh

A script file is plain text with one REPL command per line. Lines are parsed with shell-style quoting,
so quoted paths and string arguments are supported.

Small example:

    # Parse and compile
    parse_c2po specs/example.c2po
    parse_map specs/example.map
    type_check
    desugar
    optimize_rewrites
    optimize_cse
    remove_extended_operators
    multi_operators_to_binary
    assemble --print build/spec.bin

### Script Behavior Notes

- Empty lines and lines starting with `#` are ignored.
- Commands are executed in order, sharing one REPL state.
- By default, relative paths are resolved from the script file's directory.
- `push`/`pop` are valid in scripts and can checkpoint/restore state.
- `exit` ends execution early.

Example with state checkpointing:

    parse_c2po specs/example.c2po
    type_check
    push
    optimize_rewrites
    print_prefix
    pop
    compile out/spec.bin

In this example, `print_prefix` runs on the rewritten program, while the final `compile` runs after
restoring the pre-rewrite state.
