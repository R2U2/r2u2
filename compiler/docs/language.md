# C2PO Input Language
C2PO's input language is structured through the following sections:

- **INPUT**: Declare input signals and their types
- **FTSPEC**: Define future-time MLTL specifications.
- **PTSPEC**: Define past-time MLTL specifications.
- **STRUCT**: Define C-like structs
- **DEFINE**: Define macros.
- **ATOMIC**: Define atomics used by the atomic checker. (*Must compile with `--atomic-checker` flag.*)

See the example files for samples of complete, valid input.

## Formal Syntax
The best source for the formal syntax is found in the [parser](../c2po/parser.py). The allowable symbols can be derived from the `C2POLexer`, and parsing rules are found in the `C2POParser`.
