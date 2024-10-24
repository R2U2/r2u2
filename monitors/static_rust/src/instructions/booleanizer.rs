use byteorder::{LittleEndian, ByteOrder};

// Booleanizer Instruction Opcodes
pub const BZ_OP_NONE: u8 = 0b000000;
/* Loads */
pub const BZ_OP_LOAD: u8 = 0b000001;
pub const BZ_OP_STORE: u8 = 0b000010;
pub const BZ_OP_ICONST: u8 = 0b000011;
pub const BZ_OP_FCONST: u8 = 0b000100;
/* Bitwise */
pub const BZ_OP_BWNEG: u8 = 0b000101;
pub const BZ_OP_BWAND: u8 = 0b000110;
pub const BZ_OP_BWOR: u8 = 0b000111;
pub const BZ_OP_BWXOR: u8 = 0b001000;
/* Equality */
pub const BZ_OP_IEQ: u8 = 0b001001;
pub const BZ_OP_FEQ: u8 = 0b001010;
pub const BZ_OP_INEQ: u8 = 0b001011;
pub const BZ_OP_FNEQ: u8 = 0b001100;
/* Inequality */
pub const BZ_OP_IGT: u8 = 0b001101;
pub const BZ_OP_FGT: u8 = 0b001110;
pub const BZ_OP_IGTE: u8 = 0b001111;
pub const BZ_OP_FGTE: u8 = 0b010000;
pub const BZ_OP_ILT: u8 = 0b010001;
pub const BZ_OP_FLT: u8 = 0b010010;
pub const BZ_OP_ILTE: u8 = 0b010011;
pub const BZ_OP_FLTE: u8 = 0b010100;
/* Arithmetic */
pub const BZ_OP_INEG: u8 = 0b010101;
pub const BZ_OP_FNEG: u8 = 0b010110;
pub const BZ_OP_IADD: u8 = 0b010111;
pub const BZ_OP_FADD: u8 = 0b011000;
pub const BZ_OP_ISUB: u8 = 0b011001;
pub const BZ_OP_FSUB: u8 = 0b011010;
pub const BZ_OP_IMUL: u8 = 0b011011;
pub const BZ_OP_FMUL: u8 = 0b011100;
pub const BZ_OP_IDIV: u8 = 0b011101;
pub const BZ_OP_FDIV: u8 = 0b011110;
pub const BZ_OP_MOD: u8 = 0b011111;
pub const BZ_OP_IPOW: u8 = 0b100000;
pub const BZ_OP_FPOW: u8 = 0b100001;
pub const BZ_OP_ISQRT: u8 = 0b100010;
pub const BZ_OP_FSQRT: u8 = 0b100011;
pub const BZ_OP_IABS: u8 = 0b100100;
pub const BZ_OP_FABS: u8 = 0b100101;
pub const BZ_OP_PREV: u8 = 0b100110;

pub struct BooleanizerInstruction {
    pub param1: [u8; 8],
    pub param2: u32,
    pub memory_reference: u32,
    pub opcode: u8,

}

impl Copy for BooleanizerInstruction{ }

impl Clone for BooleanizerInstruction{
    fn clone(&self) -> BooleanizerInstruction {
        return *self
    }
}

impl BooleanizerInstruction {
    pub fn set_from_binary(instr: &[u8]) -> BooleanizerInstruction{
        return BooleanizerInstruction{ 
            param1: [instr[0], instr[1], instr[2], instr[3], instr[4], instr[5], instr[6], instr[7]],
            param2: LittleEndian::read_u32(&instr[8..]),
            memory_reference: LittleEndian::read_u32(&instr[12..]),
            opcode: instr[16],
        };
    }
    pub fn empty_instr() -> BooleanizerInstruction{
        return BooleanizerInstruction{ 
            param1: [0; 8],
            param2: 0,
            memory_reference: 0,
            opcode: BZ_OP_NONE,
        };
    }
}