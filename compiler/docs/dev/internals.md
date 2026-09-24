# Internal Architecture

C2PO is now organized around a command registry and shared compiler state, instead of a single
hard-coded pass list.

At runtime, `c2po/main.py` builds a `CommandConsole` with:

- a `cpt.Program` (current specification graph)
- a `cpt.Context` (symbol tables, mappings, stats, solver paths, assembly output, etc.)
- all registered commands from `c2po/command.py` and module-level command registrations

The same command system is used by:

- interactive REPL mode (`--interactive`)
- script mode (`--script`)
- top-level CLI mode (`--spec ...`) via a generated temporary script

## Compilation Flow

In CLI mode (`c2po.main.cli`), behavior is assembled from command invocations based on flags.
The typical flow is:

1. Parse input (`parse_c2po` or `parse_mltl`)
2. Optional trace/map parsing (`parse_trace`, `parse_map`)
3. Type check (`type_check`)
4. Desugar (`desugar`)
5. Optional optimization stage (`optimize_eqsat` or `optimize_rewrites`)
6. Optional transforms (`remove_extended_operators`, `optimize_cse`)
7. Optional SMT checks (`check_sat`)
8. Lowering for assembly (`multi_operators_to_binary`, `remove_extended_operators`)
9. Assembly/output (`assemble`, optional bounds writers)

Composite commands (for example `compile` and `assemble`) are defined in code and expand into
ordered subcommands.

## Guard Conditions

Commands can declare guard preconditions (for example: `DESUGARED`, `COMPUTED_ATOMICS`,
`ONLY_BINARY_OPERATORS`). Guard checks are centralized in `c2po/command.py`.

If a guard fails in REPL/script mode, C2PO reports the missing condition and suggests commands
that typically satisfy it.

## Serialization and Output

Serialization/output capabilities are commands, not a separate pipeline stage. Common ones:

- `write_c2po`
- `write_mltl`
- `write_prefix`
- `write_pickle`
- `assemble` (binary + optional assembly text)
- `write_bounds_c` / `write_bounds_rust`