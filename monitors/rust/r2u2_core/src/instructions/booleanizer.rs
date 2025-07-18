use byteorder::{LittleEndian, ByteOrder};

// Booleanizer Instruction Opcodes
pub const BZ_OP_NONE: u8 = 0b000000;
/* Loads */
pub const BZ_OP_ILOAD: u8 = 0b000001;
pub const BZ_OP_FLOAD: u8 = 0b000010;
pub const BZ_OP_ICONST: u8 = 0b000011;
pub const BZ_OP_FCONST: u8 = 0b000100;
/* Store */
pub const BZ_OP_STORE: u8 = 0b0000101;
/* Bitwise */
pub const BZ_OP_BWNEG: u8 = 0b000110;
pub const BZ_OP_BWAND: u8 = 0b000111;
pub const BZ_OP_BWOR: u8 = 0b001000;
pub const BZ_OP_BWXOR: u8 = 0b001001;
/* Equality */
pub const BZ_OP_IEQ: u8 = 0b001010;
pub const BZ_OP_FEQ: u8 = 0b001011;
pub const BZ_OP_INEQ: u8 = 0b001100;
pub const BZ_OP_FNEQ: u8 = 0b001101;
/* Inequality */
pub const BZ_OP_IGT: u8 = 0b001110;
pub const BZ_OP_FGT: u8 = 0b001111;
pub const BZ_OP_IGTE: u8 = 0b010000;
pub const BZ_OP_FGTE: u8 = 0b010001;
pub const BZ_OP_ILT: u8 = 0b010010;
pub const BZ_OP_FLT: u8 = 0b010011;
pub const BZ_OP_ILTE: u8 = 0b010100;
pub const BZ_OP_FLTE: u8 = 0b010101;
/* Arithmetic */
pub const BZ_OP_INEG: u8 = 0b010110;
pub const BZ_OP_FNEG: u8 = 0b010111;
pub const BZ_OP_IADD: u8 = 0b011000;
pub const BZ_OP_FADD: u8 = 0b011001;
pub const BZ_OP_ISUB: u8 = 0b011010;
pub const BZ_OP_FSUB: u8 = 0b011011;
pub const BZ_OP_IMUL: u8 = 0b011100;
pub const BZ_OP_FMUL: u8 = 0b011101;
pub const BZ_OP_IDIV: u8 = 0b011110;
pub const BZ_OP_FDIV: u8 = 0b011111;
pub const BZ_OP_MOD: u8 = 0b100000;
pub const BZ_OP_IPOW: u8 = 0b100001;
pub const BZ_OP_FPOW: u8 = 0b100010;
pub const BZ_OP_ISQRT: u8 = 0b100011;
pub const BZ_OP_FSQRT: u8 = 0b100100;
pub const BZ_OP_IABS: u8 = 0b100101;
pub const BZ_OP_FABS: u8 = 0b100110;
pub const BZ_OP_PREV: u8 = 0b100111;
pub const BZ_TS: u8 = 0b101000;

#[derive(Copy, Clone)]
pub struct BooleanizerInstruction {
    pub param1: u32,
    pub param2: u32,
    pub memory_reference: u32,
    pub opcode: u8,

}

impl BooleanizerInstruction { // C2PO format sensitive
    pub fn get_param1_int_from_binary(instr: &[u8]) -> i32 {
        return LittleEndian::read_i32(&instr[0..]);
    }
    pub fn get_param1_float_from_binary(instr: &[u8]) -> f64 {
        return LittleEndian::read_f64(&instr[0..]);
    }
    pub fn set_from_binary(instr: &[u8]) -> BooleanizerInstruction{
        return BooleanizerInstruction{ 
            param1: LittleEndian::read_u32(&instr[0..]),
            param2: LittleEndian::read_u32(&instr[8..]),
            memory_reference: LittleEndian::read_u32(&instr[12..]),
            opcode: instr[16],
        };
    }
    pub fn empty_instr() -> BooleanizerInstruction{
        return BooleanizerInstruction{ 
            param1: 0,
            param2: 0,
            memory_reference: 0,
            opcode: BZ_OP_NONE,
        };
    }
}