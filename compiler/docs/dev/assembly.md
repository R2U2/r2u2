# Assembler

C2PO generates assembly and packs that assembly into a binary representation using the [struct
library](https://docs.python.org/3/library/struct.html) that R2U2 then uses to monitor input data
against.

The implementation lives in `c2po/assemble.py`:

- `gen_assembly(...)` builds typed instruction objects (`BZInstruction`, `TLInstruction`,
  `CGInstruction`, and optional alias instructions)
- packing functions convert instruction fields to binary using `field_format_str_map`
- `assemble(...)` writes:
  - required spec binary
  - optional human-readable assembly (`--assembly-filename` or `--print`)
  - optional aux alias table (`--aux` / `--no-aux`)

## Commands

- `assemble`: composite command that runs `compute_atomics`, `compute_scq_sizes`, then
  `unsafe_assemble`
- `unsafe_assemble`: performs only assembly/emission, and requires guard conditions to already be
  satisfied

The assembler expects a desugared, binary-operator-ready program with valid atomics and SCQ sizing.

Use debug logging when modifying this path:

    python3 c2po.py --spec example.c2po --debug
