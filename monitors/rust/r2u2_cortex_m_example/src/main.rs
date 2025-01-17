#![no_std]
#![no_main]

use internals::SPEC;
use internals::button::UserButton;
use panic_halt as _;

use cortex_m_rt::entry;
use cortex_m_semihosting::hprintln;
use cortex_m::peripheral::NVIC;
use r2u2_core;

#[cfg(feature = "calculate_cycles")]
use stm32f3xx_hal::pac::DWT;

use core::cell::{RefCell};
use critical_section::Mutex;
use stm32f3xx_hal::time::duration::{Milliseconds};
use stm32f3xx_hal::{timer, timer::Timer, interrupt, pac, prelude::*};
use switch_hal::InputSwitch;

mod internals;

/// Timer  from TIM3.
static TIMER: Mutex<RefCell<Option<Timer<pac::TIM3>>>> = Mutex::new(RefCell::new(None));

/// Determines how often the timer interrupt should fire. 
const TIM3_WAKE_UP_EVERY_MS: Milliseconds = Milliseconds(10);

static mut RUN_R2U2: bool = false;

#[entry]
fn main() -> ! {
    hprintln!("Hello!");
    #[cfg(feature = "calculate_cycles")]
    let mut cp = cortex_m::Peripherals::take().unwrap();

    let dp = pac::Peripherals::take().unwrap();
    let mut flash = dp.FLASH.constrain();
    let mut rcc = dp.RCC.constrain();

    let clocks = rcc
        .cfgr
        .use_hse(8.MHz())
        .sysclk(48.MHz())
        .pclk1(24.MHz())
        .pclk2(24.MHz())
        .freeze(&mut flash.acr);

    // Configure the on-board LED (LD3, north red)
    let mut gpioe = dp.GPIOE.split(&mut rcc.ahb);
    let mut led_red = gpioe
        .pe9
        .into_push_pull_output(&mut gpioe.moder, &mut gpioe.otyper);
    led_red.set_low().ok(); // Turn off

    // Configure the on-board LED (L6, west green)
    let mut led_green = gpioe
        .pe15
        .into_push_pull_output(&mut gpioe.moder, &mut gpioe.otyper);
    led_green.set_low().ok(); // Turn off

    // initialize user button
    let mut gpioa = dp.GPIOA.split(&mut rcc.ahb);
    let button = UserButton::new(gpioa.pa0, &mut gpioa.moder, &mut gpioa.pupdr);

    // Configure a timer to generate interrupts.
    let mut timer = Timer::new(dp.TIM3, clocks, &mut rcc.apb1);
    let timer_interrupt = timer.interrupt();

    timer.enable_interrupt(timer::Event::Update);
    timer.start(TIM3_WAKE_UP_EVERY_MS);

    // Put the timer in the global context.
    critical_section::with(|cs| {
        TIMER.replace(cs, Some(timer));
    });

    unsafe {
        NVIC::unmask(timer_interrupt);
    }

    #[cfg(feature = "calculate_cycles")] {
        cp.DCB.enable_trace();
        cp.DWT.enable_cycle_counter();
    }

    let mut monitor = r2u2_core::get_monitor(&SPEC);
    hprintln!("Initialized monitor!");
    loop{
        unsafe{
            if RUN_R2U2 {
                r2u2_core::load_bool_signal(&mut monitor, 0, button.is_active().expect("Error with button"));
                #[cfg(feature = "calculate_cycles")]
                let cycles = DWT::cycle_count();
                r2u2_core::monitor_step(&mut monitor);
                #[cfg(feature = "calculate_cycles")] {
                    let cycles = DWT::cycle_count() - cycles;
                    hprintln!("{}", cycles);
                }
                for out in r2u2_core::get_output_buffer(&mut monitor).iter() {
                    if out.spec_num == 0 { // G[0,500] button
                        if out.verdict.truth {
                            led_red.set_high().ok();
                        } else {
                            led_red.set_low().ok();
                        }
                    } else if out.spec_num == 1 { // O[0,500] button
                        if out.verdict.truth {
                            led_green.set_high().ok();
                        } else {
                            led_green.set_low().ok();
                        }
                    }
                    //hprintln!("{}:{},{}", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
                }
                RUN_R2U2 = false;
            }
        }
    }
}

#[interrupt]
fn TIM3() {

    unsafe{
        RUN_R2U2 = true;
    }

    // Just handle the pending interrupt event.
    critical_section::with(|cs| {
        if let Some(ref mut timer) = TIMER.borrow_ref_mut(cs).as_mut() {
            // Finally operate on the timer itself.
            timer.clear_event(timer::Event::Update);
        }
    })
}