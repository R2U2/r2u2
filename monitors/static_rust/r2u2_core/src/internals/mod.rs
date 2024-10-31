use core::default;

#[cfg(embedded)]
pub mod stm32_f3_discovery_usb_interface;

pub mod bounds;
pub mod debug;
pub mod process_binary;
pub mod types;