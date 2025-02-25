#[cfg(feature = "aux_string_specs")]
use fixedstr::{ztr64, ztr128};

#[cfg(feature = "aux_string_specs")]
fn convert_ascii_to_decimal(ascii: &[u8]) -> u32 {
    let mut num: u32 = 0;
    let mut multiplier: u32 = 1;
    for x in (0..ascii.len()).rev() {
        num += (ascii[x] as char).to_digit(10).unwrap_or(0) * multiplier;
        multiplier *= 10;
    }
    return num;
}

#[cfg(feature = "aux_string_specs")]
pub struct AuxiliaryInfo {
    // Spec String and Spec Number(s)
    pub spec_str: ztr64,
    pub spec_0: u32, 
    pub spec_1: u32,
    pub spec_2: u32,
}

#[cfg(feature = "aux_string_specs")]
impl Copy for AuxiliaryInfo { }

#[cfg(feature = "aux_string_specs")]
impl Clone for AuxiliaryInfo {
    fn clone(&self) -> AuxiliaryInfo {
        return *self
    }
}

#[cfg(feature = "aux_string_specs")]
impl Default for AuxiliaryInfo {
    fn default() -> Self {
        return AuxiliaryInfo {
            spec_str: ztr64::from(""),
            spec_0: 0, 
            spec_1: 0,
            spec_2: 0,
        }
    }
}

#[cfg(feature = "aux_string_specs")]
impl AuxiliaryInfo {
    pub fn set_contract(instr: &[u8]) -> (AuxiliaryInfo, usize) {
        let mut contract = AuxiliaryInfo::default();
        let aux_data = ztr128::from_raw(&instr[2..]);

        let mut start = 0;
        let mut end = aux_data.find(' ').unwrap_or(64);
        contract.spec_str = aux_data.substr(start, end).resize();

        start = end + 1;
        end = start + aux_data.substr(start, aux_data.len()).find(' ').unwrap_or(aux_data.len());
        contract.spec_0 = convert_ascii_to_decimal(&instr[start+2..end+2]);

        start = end + 1;
        end = start + aux_data.substr(start, aux_data.len()).find(' ').unwrap_or(aux_data.len());
        
        contract.spec_1 = convert_ascii_to_decimal(&instr[start+2..end+2]);

        start = end + 1;
        end = aux_data.len();
        
        contract.spec_2 = convert_ascii_to_decimal(&instr[start+2..end+2]);
        return (contract, aux_data.len() + 2);
    }
    pub fn set_function(instr: &[u8]) -> (AuxiliaryInfo, usize) {
        let mut contract = AuxiliaryInfo::default();
        let aux_data = ztr128::from_raw(&instr[2..]);

        let mut start = 0;
        let mut end = aux_data.find(' ').unwrap_or(64);
        contract.spec_str = aux_data.substr(start, end).resize();

        start = end + 1;
        end = aux_data.len();
        contract.spec_0 = convert_ascii_to_decimal(&instr[start+2..end+2]);
        return (contract, aux_data.len() + 2);
    }
}