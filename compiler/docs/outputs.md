# C2PO Output Formats
C2PO supports a number of formats to output (dump) a specification. By default, C2PO will output the R2U2 binary format, but can be configured to output other file formats as well.

See the table below for each format and option to pass to output it. Note that R2U2 binary is output by default, so its option will **disable** it. All these options are compatible with one another, so passing all options will output all file formats given.

| Format | C2PO Option |
|--------|-------------|
| [R2U2 Binarys (TODO)](./) | (To disable) `--disable-assemble` |
| [MLTL-STD](./mltl_std.md) | `--dump-mltl` |
| [Pickle](https://docs.python.org/3/library/pickle.html) | `--dump-pickle` |

