use super::types::r2u2_float;

// Size of binary instruction file that can be read
pub const SPEC_FILE_MAX_SIZE: usize = 1028;

pub const R2U2_MAX_SIGNALS: usize = 256;
pub const R2U2_MAX_ATOMICS: usize = 256;
pub const R2U2_MAX_BZ_INSTRUCTIONS: usize = 256;
pub const R2U2_MAX_TL_INSTRUCTIONS: usize = 256;
pub const R2U2_TOTAL_QUEUE_MEM: usize = (256 * 1024);

pub const R2U2_FLOAT_EPSILON: r2u2_float =  0.00001;