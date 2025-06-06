#![allow(non_camel_case_types)]

#[cfg(feature = "aux_string_specs")]
use fixedstr::ztr64;

use vstd::prelude::*;

verus! {

// Assume-guarantee contract status
#[cfg(feature = "aux_string_specs")]
/// Assume-Guarantee Contract (AGC) inactive status
pub const AGC_INACTIVE: u8 = 0;
#[cfg(feature = "aux_string_specs")]
/// Assume-Guarantee Contract (AGC) invalid status
pub const AGC_INVALID: u8 = 1;
#[cfg(feature = "aux_string_specs")]
/// Assume-Guarantee Contract (AGC) verified status
pub const AGC_VERIFIED: u8 = 2;

pub type r2u2_time = u32;

pub type r2u2_float = f64;

pub type r2u2_bool = bool;

pub type r2u2_int = i32;

pub type r2u2_addr = u32;

#[allow(non_upper_case_globals)]
pub const r2u2_infinity: r2u2_time = r2u2_time::MAX;

#[derive(Copy, Clone)]
/// Struct to contain verdict-timestamp tuples
pub struct r2u2_verdict{
    // Time & Truth
    pub time: r2u2_time,
    pub truth: bool, 
}

impl Default for r2u2_verdict{
    fn default() -> Self {
        return r2u2_verdict {
            time: r2u2_infinity,
            truth: false,
        }
    }
}

#[verifier::external] // Verus doesn't support floats
#[derive(Copy, Clone)]
pub struct r2u2_value{
    // Notice that we store booleans as integers so we do not require 
    // boolean specific instructions (e.g., BLOAD or BADD)
    pub i: r2u2_int,
    pub f: r2u2_float,
}

#[verifier::external] // Verus doesn't support floats
impl Default for r2u2_value{
    fn default() -> Self {
        return r2u2_value {
            i: 0,
            f: 0.0,
        }
    }
}

#[derive(Copy, Clone)]
/// Struct to contain output verdicts (i.e., specification identification and verdict)
pub struct r2u2_output{
    // Spec Number/Name & Verdict
    pub spec_num: r2u2_addr,
    #[cfg(feature = "aux_string_specs")]
    pub spec_str: ztr64,
    pub verdict: r2u2_verdict, 
}

impl Default for r2u2_output{
    fn default() -> Self {
        return r2u2_output {
            spec_num: r2u2_infinity,
            #[cfg(feature = "aux_string_specs")]
            spec_str: ztr64::from(""),
            verdict: r2u2_verdict::default(),
        }
    }
}

#[cfg(feature = "aux_string_specs")]
#[derive(Copy, Clone)]
/// Struct to contain Assume-Guarantee Contract (AGC) verdicts (i.e., contract identification and status)
pub struct r2u2_contract{
    // Spec Number & Verdict
    pub spec_str: ztr64,
    pub time: r2u2_time,
    pub status: u8, // 0 = active, 1 = valid, 2 = verified 
}

#[cfg(feature = "aux_string_specs")]
impl Default for r2u2_contract {
    fn default() -> Self {
        return r2u2_contract {
            spec_str: ztr64::from(""),
            time: r2u2_infinity,
            status: AGC_INACTIVE,
        }
    }
}

}