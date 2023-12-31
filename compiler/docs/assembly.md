# C2PO Assembler

C2PO generates assembly and packs that assembly into a binary representation using the [struct library](https://docs.python.org/3/library/struct.html) that R2U2 then uses to monitor input data against. The `generate_assembly` function takes an AST as input and generates a list of assembly instruction objects. Each instruction is then packed according to the defined C data representations in the `field_format_str_map` dictionary. 

The `--debug` option can be particularly useful when modifying the assembler.
