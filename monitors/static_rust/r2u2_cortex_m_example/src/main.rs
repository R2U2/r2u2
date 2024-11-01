#![no_std]
#![no_main]

use panic_halt as _;

use cortex_m_rt::entry;
use cortex_m_semihosting::hprintln;

mod internals;

#[entry]
fn main() -> ! {
    hprintln!("Hello, world");
    internals::stm32_f3_discovery_usb_interface::read_binary_file();
    loop {}
}