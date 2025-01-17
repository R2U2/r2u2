use crate::internals::types::r2u2_float;
use const_env::from_env;

/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_SPECS = { value = "32", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_MAX_SPECS: usize = 256;

/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_SIGNALS = { value = "64", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_MAX_SIGNALS: usize = 256;

/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_ATOMICS = { value = "128", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_MAX_ATOMICS: usize = 256;

/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_BZ_INSTRUCTIONS = { value = "256", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_MAX_BZ_INSTRUCTIONS: usize = 256;

/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_TL_INSTRUCTIONS = { value = "256", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_MAX_TL_INSTRUCTIONS: usize = 256;

/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_TOTAL_QUEUE_MEM = { value = "1024", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_TOTAL_QUEUE_MEM: usize = 2048;

pub const R2U2_FLOAT_EPSILON: r2u2_float =  0.00001;