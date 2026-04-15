# Parser

C2PO uses [SLY](https://sly.readthedocs.io/en/latest/sly.html) lexers/parsers for all front-end
formats.

Current parser entry points:

- `c2po/parse_c2po.py`: native C2PO language (`.c2po`)
- `c2po/parse_mltl.py`: MLTL standard input (`.mltl`)
- `c2po/parse_equiv.py`: equivalence input format (`.equiv`)

Each parser is exposed as a command (`parse_c2po`, `parse_mltl`, `parse_equiv`) that returns a
`cpt.Program` and updates relevant fields in `cpt.Context` (for example signal mappings, symbolic
bounds/constraints in `.equiv`, and source filename metadata).

Parsing focuses on syntax construction. Most semantic validation and type enforcement are deferred
to `type_check`.