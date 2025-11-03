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
#[derive(Copy, Clone)]
pub struct FormulaAuxiliaryInfo {
    // Spec String and Spec Number
    pub spec_str: ztr64,
    pub spec: u32, 
}

#[cfg(feature = "aux_string_specs")]
impl Default for FormulaAuxiliaryInfo {
    fn default() -> Self {
        return FormulaAuxiliaryInfo {
            spec_str: ztr64::from(""),
            spec: 0, 
        }
    }
}

#[cfg(feature = "aux_string_specs")]
impl FormulaAuxiliaryInfo {
    pub fn set_function(instr: &[u8]) -> (FormulaAuxiliaryInfo, usize) {
        let mut contract = FormulaAuxiliaryInfo::default();
        let aux_data = ztr128::from_raw(&instr[2..]);

        let mut start = 0;
        let mut end = aux_data.find(' ').unwrap_or(64);
        contract.spec_str = aux_data.substr(start, end).resize();

        start = end + 1;
        end = aux_data.len();
        contract.spec = convert_ascii_to_decimal(&instr[start+2..end+2]);
        return (contract, aux_data.len() + 2);
    }
}

#[cfg(feature = "aux_string_specs")]
#[derive(Copy, Clone)]
pub struct ContractAuxiliaryInfo {
    // Spec String and Spec Numbers
    pub spec_str: ztr64,
    pub spec_0: u32, 
    pub spec_1: u32,
    pub spec_2: u32,
}

#[cfg(feature = "aux_string_specs")]
impl Default for ContractAuxiliaryInfo {
    fn default() -> Self {
        return ContractAuxiliaryInfo {
            spec_str: ztr64::from(""),
            spec_0: 0, 
            spec_1: 0,
            spec_2: 0,
        }
    }
}

#[cfg(feature = "aux_string_specs")]
impl ContractAuxiliaryInfo {
    pub fn set_contract(instr: &[u8]) -> (ContractAuxiliaryInfo, usize) {
        let mut contract = ContractAuxiliaryInfo::default();
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
}