use crate::internals::types::r2u2_float;
use const_env::from_env;

/// Represents maximum number of output verdicts that can be returned at a single timestamp
/// 
/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_OUTPUT_VERDICTS = { value = "32", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_MAX_OUTPUT_VERDICTS: usize = 256;

/// Represents maximum number of output contract statuses that can be returned at a single timestamp (only utilized when aux_string_specs feature is enabled)
/// 
/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_OUTPUT_CONTRACTS = { value = "32", force = true }
/// ```
/// 
#[cfg(feature = "aux_string_specs")]
#[from_env]
pub const R2U2_MAX_OUTPUT_CONTRACTS: usize = 128;

/// Represents maximum number of specifications being monitored (only utilized when aux_string_specs feature is enabled)
/// 
/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_MAX_SPECS = { value = "32", force = true }
/// ```
/// 
#[cfg(feature = "aux_string_specs")]
#[from_env]
pub const R2U2_MAX_SPECS: usize = 256;

/// Represents maximum number of input signals
/// 
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

/// Represents maximum number of Booleans passed from the front-end (booleanizer or directly loaded atomics) to the temporal logic engine
/// 
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

/// Represents maximum number of booleanizer instructions
/// 
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

/// Represents maximum number of temporal logic instructions
/// 
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

/// Represents total number of SCQ slots for both future-time and past-time reasoning
/// 
/// Adjust by setting in .cargo/config.toml of parent project
/// 
/// # Examples
/// ```
/// [env]
/// R2U2_TOTAL_QUEUE_SLOTS = { value = "1024", force = true }
/// ```
/// 
#[from_env]
pub const R2U2_TOTAL_QUEUE_SLOTS: usize = 2048;

pub const R2U2_FLOAT_EPSILON: r2u2_float =  0.00001;