# Output Formats

C2PO can emit multiple output formats, but they are produced in two different ways:

- **CLI mode (`python3 c2po.py --spec ...`)**: writes the assembled R2U2 binary (`--output`), and
  optionally bounds (`--write-bounds`).
- **REPL/script mode (`--interactive` / `--script`)**: writes the other representations using REPL
  commands such as `write_c2po`, `write_prefix`, `write_mltl`, and `write_pickle`.

| Format                                                  | How to Generate | Reason to use |
|---------------------------------------------------------|-----------------|---------------|
| R2U2 Binary                                             | CLI `--output` or REPL/script `assemble` | Run R2U2 over specification |
| [C2PO](./language.md)                                   | REPL/script `write_c2po <filename>` | Validate the specification post-compilation or debugging |
| [Prefix Notation C2PO](./language.md)                   | REPL/script `write_prefix <filename>` | Validate the specification post-compilation or debugging. Some operators have multiple arities, so `(&& a b c)` is a conjunction applied to three arguments. In infix notation this is `a && b && c`, which is more difficult to discern. This can affect SCQ sizing analysis. |
| [MLTL-STD](./mltl_std.md)                               | REPL/script `write_mltl <filename>` | Convert C2PO files to MLTL-STD files |
| [Pickle](https://docs.python.org/3/library/pickle.html) | REPL/script `write_pickle <filename>` | Compare program properties like memory requirements across different C2PO calls |

Example script snippet:

    parse_c2po spec.c2po
    compile out/spec.bin
    write_c2po out/spec.c2po
    write_prefix out/spec.prefix
    write_mltl out/spec.mltl
    write_pickle out/spec.pickle
