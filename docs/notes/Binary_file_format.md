# Binary file format
<Offset to next offset> R2U2 <Version> <Compiler Info> <Monitor Info> <0x00>
<offset to next offset> <one byte tag> aribritrary bytes


Header: data[1] to data[data[0] - 1]
First Inst: data[data[0]] to data[data[data[0]] - 1]
2nd Inst: data[data[data[0]]] to data[data[data[data[0]]]]

inst tabl:  Tag, First byte, length
  | PC[0] = {data[data[0] + 1], &(data[data[0]]+2), data[data[data[0]]]}
  | PC[1] = {}
  | PC[2] = {}

Byte oriented (all suporrted paltforms address to the byte)

Limitations & assumptions:
Instrucitons can be at most 254 bytes long (i.e., offset of 255 must reach next instruction)
Offset of 0 for EOF

Since header must be present, initial offset can't be zero but you
can set it to point to the header string's null terminator for an
easy "empty file" that can pass ehader checks