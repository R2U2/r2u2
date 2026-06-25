# R2U2 Configuration Binary Files [`.bin`]

The R2U2 configuration binary format is produced by C2PO and configures a monitor to verify a set specifications.

## Format
There are three sections in the specification file
1. Header
2. Instructions
3. Auxiliary Statements

The first two sections uses a chain of offsets to separate the variable-width fields wherein the first byte indicates the number of bytes away the next offset byte is located.
This forms a linked list where the gaps between the offset bytes contain data.
The length of the field is therefore is the offset - 1.
An offset of zero is used to indicate the end of the instruction section.

### Header
The header consists of UTF-8 encoded text in the following layout, terminating with a null byte:
```
<Offset to next offset> R2U2 <Version> <Compiler Info> <Monitor Info> <0x00>
```
Where the version refers to the R2U2 framework version for compatibility checking, while the compiler and monitor info fields provide information on the configuration options used by the specification.

### Instructions
The instruction memory consists of monitor instructions prefixed by a one-byte engine tag identifying the format of the following instructions, followed by arbitrary bytes as defined by each engine's instruction format as shown:
```
<Offset to next offset> <one byte engine tag> <arbitrary bytes>
```

One special case is the "configuration" engine, which is a tag that instructs the monitor to execute the following bytes as a engine tag prefixed instruction once immediately, but not during monitoring.
These are used by engines to initialize memory values such as buffer sizes and temporal bounds.
The resulting format becomes:
```
<Offset to next offset> <one byte config tag> <one byte engine tag> <arbitrary bytes>
```

After all the instructions, an offset of zero is used to signify the end of the program.
In an naive traversal of the linked-list, this would result in an infinite loop.

### Auxiliary Statements
After the instruction section ends, optional auxiliary statements may be present.
Each auxiliary statement is a UTF-8 encoded, null-terminated, string starting with a single character representing the type of the statement, followed by space-delineated fields as defined by the type.

These are intentionally structured to be easy to parse with `scanf` by first switching case based on the leading character then using a type appropriate format string to extract the remaining field values.

## Example Layout
A rough outline of the complete layout:
```
<offset to next offset> R2U2 <Version> <Compiler Info> <Monitor Info> <0x00>
<offset to next offset> <Offset to next offset> <one byte config tag> <arbitrary bytes>
<offset to next offset> <Offset to next offset> <one byte config tag> <arbitrary bytes>
<offset to next offset> <one byte engine tag> <arbitrary bytes>
<offset to next offset> <one byte engine tag> <arbitrary bytes>
<0x00>
F 1 Formula_Name <0x00>
C Contract_name 1 2 3 <0x00>
```

---

## Limitations & Assumptions

Instructions can be at most 254 bytes long (i.e., offset of 255 must reach next instruction)

Offset of 0 is used to signify end of the instruction section.

Since header must be present, initial offset can't be zero but you can set it to point to the header string's null terminator for an easy "empty file" that can pass header checks.

All formulas auxilary statements (specified with 'F') always appear in-order before contract auxiliary statements (specified with 'C') in the binary

All CG TL SCQ instructions must be placed before CG TL TEMP instructions to always completely configure the SCQ size for all SCQ's before configuring temporal metadata

All PREV booleanizer instructions are at the end of the booleanizer instruction list to always update the 'previous value' after current iteration.

## Decoding Hints
```
Header: data[1] to data[data[0] - 1]
First Inst: data[data[0]] to data[data[data[0]] - 1]
2nd Inst: data[data[data[0]]] to data[data[data[data[0]]]]

Instruction Table:  Tag, First byte, length
  | PC[0] = {data[data[0] + 1], &(data[data[0]]+2), data[data[data[0]]]}
  | PC[1] = {}
  | PC[2] = {}
```