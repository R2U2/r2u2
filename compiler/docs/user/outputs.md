# Output Formats

C2PO supports a number of formats to output (write) a specification. By default, C2PO will output
the R2U2-readable binary format, but can be configured to output other formats as well.

See the table below for each format and option to pass to output it. Note that R2U2 binary is output
by default, so its option will **disable** it. All these options are compatible with one another, so
passing all options will output all file formats given.

| Format                                                  | C2PO CLI Option                   | Reason to use |
|---------------------------------------------------------|-----------------------------------|---------------|
| R2U2 Binary                                             | (To disable) `--disable-assemble` | Run R2U2 over specification |
| [C2PO](./language.md)                                   | `--write-c2po`                    | Validate the specification post-compilation or debugging
| [Prefix Notation C2PO](./language.md)                   | `--write-prefix`                  | Validate the specification post-compilation or debugging. Some operators have multiple arities, so `(&& a b c)` is a conjunction applied to three arguments. In infix notation this is `a && b && c` which is more difficult to discern. This can have impacts on things like SCQ sizing. |
| [MLTL-STD](./mltl_std.md)                               | `--write-mltl`                    | Convert C2PO files to MLTL-STD files. |
| [Pickle](https://docs.python.org/3/library/pickle.html) | `--write-pickle`                  | Compare program properties like memory requirements across different C2PO calls. |

Each option can be followed by a filename to write the output to, otherwise it writes it to the
filename with the extension changed to match.
