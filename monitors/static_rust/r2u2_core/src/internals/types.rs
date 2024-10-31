#[allow(non_camel_case_types)]
pub type r2u2_time = u32;

#[allow(non_camel_case_types)]
pub type r2u2_float = f64;

#[allow(non_camel_case_types)]
pub type r2u2_bool = bool;

#[allow(non_camel_case_types)]
pub type r2u2_int = i32;

#[allow(non_upper_case_globals)]
pub const r2u2_infinity: r2u2_time = r2u2_time::MAX;

#[allow(non_camel_case_types)]
pub struct r2u2_verdict{
    // Time & Truth
    pub time: r2u2_time,
    pub truth: bool, 
}

impl Copy for r2u2_verdict{ }

impl Clone for r2u2_verdict{
    fn clone(&self) -> r2u2_verdict {
        return *self
    }
}

impl Default for r2u2_verdict{
    fn default() -> Self {
        return r2u2_verdict {
            time: r2u2_infinity,
            truth: false,
        }
    }
}

pub struct r2u2_value{
    // Notice that we store booleans as integers so we do not require 
    // boolean specific instructions (e.g., BLOAD or BADD)
    pub i: r2u2_int,
    pub f: r2u2_float,
}

impl Copy for r2u2_value{ }

impl Clone for r2u2_value{
    fn clone(&self) -> r2u2_value {
        return *self
    }
}

impl Default for r2u2_value{
    fn default() -> Self {
        return r2u2_value {
            i: 0,
            f: 0.0,
        }
    }
}