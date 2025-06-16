# `r2u2_cortex_m_example`

> A simple example for running R2U2 on ARM Cortex-M microcontrollers (specifically targets the STM32F3DISCOVERY board)

> The green west LED (LD6) lights up when Once[0,500] USER button evaluates to TRUE, or Once[0,5s] USER button since R2U2 is run every 50 milliseconds.
> The red north LED (LD3) lights up when Global[0,500] USER button evaluates to TRUE, or Global[0,5s] USER button since R2U2 is run every 50 milliseconds.

<div align="center">
  <img src="demo_led_button.gif" alt="LEDs triggered by R2U2 based on button on STM32F3 Discovery board"/>
</div>

## Dependencies

To build embedded programs using this example you'll need:

- Rust 1.79 or newer. ([Installation
  instructions](https://rustup.rs/)).

- GDB arm debugger 

- `openocd`

- `rust-std` components (pre-compiled `core` crate) for the ARM Cortex-M
  targets. Run:

``` console
$ rustup target add thumbv7em-none-eabihf
```

- `flip-link` to add zero-cost stack overflow protection  (https://github.com/knurling-rs/flip-link). Run:
``` console
$ cargo install flip-link
```

## Using this example

**NOTE**: For more information on how to run embedded Rust programs on a Cortex-M microcontroller, refer to [The Embedded Rust Book](https://rust-embedded.github.io/book).

**NOTE**: This example was built off the [cortex-m-quickstart](https://github.com/rust-embedded/cortex-m-quickstart/tree/master) example.


0. Before we begin you need to identify some characteristics of the target
  device as these will be used to configure the project:

- The ARM core. e.g. Cortex-M3.

- Does the ARM core include an FPU? Cortex-M4**F** and Cortex-M7**F** cores do.

- How much Flash memory and RAM does the target device has? e.g. 256 KiB of
  Flash and 32 KiB of RAM.

- Where are Flash memory and RAM mapped in the address space? e.g. RAM is
  commonly located at address `0x2000_0000`.

You can find this information in the data sheet or the reference manual of your
device.

In this example we'll be using the STM32F3DISCOVERY. This board contains an
STM32F303VCT6 microcontroller. This microcontroller has:

- A Cortex-M4F core that includes a single precision FPU

- 256 KiB of Flash located at address 0x0800_0000.

- 40 KiB of RAM located at address 0x2000_0000. (There's another RAM region but
  for simplicity we'll ignore it).

1. Set a default compilation target. There are four options as mentioned at the
   bottom of `.cargo/config`. For the STM32F303VCT6, which has a Cortex-M4F
   core, we'll pick the `thumbv7em-none-eabihf` target.

``` toml
[build]
# Pick ONE of these compilation targets
# target = "thumbv6m-none-eabi"    # Cortex-M0 and Cortex-M0+
# target = "thumbv7m-none-eabi"    # Cortex-M3
# target = "thumbv7em-none-eabi"   # Cortex-M4 and Cortex-M7 (no FPU)
target = "thumbv7em-none-eabihf" # Cortex-M4F and Cortex-M7F (with FPU)
# target = "thumbv8m.base-none-eabi"   # Cortex-M23
# target = "thumbv8m.main-none-eabi"   # Cortex-M33 (no FPU)
# target = "thumbv8m.main-none-eabihf" # Cortex-M33 (with FPU)
```

2. Configure R2U2's memory in `.cargo/config.toml`. For this example, the following is required:

``` toml
[env]
R2U2_MAX_SPECS = { value = "2", force = true }
R2U2_MAX_SIGNALS = { value = "1", force = true }
R2U2_MAX_ATOMICS = { value = "1", force = true }
R2U2_MAX_BZ_INSTRUCTIONS = { value = "1", force = true }
R2U2_MAX_TL_INSTRUCTIONS = { value = "8", force = true }
R2U2_TOTAL_QUEUE_MEM = { value = "8", force = true }
```

**NOTE**: If these values are changed, run `$ cargo clean`.

3. Enter the memory region information into the `memory.x` file.

``` file
MEMORY
{
  /* NOTE 1 K = 1 KiBi = 1024 bytes */
  /* TODO Adjust these memory regions to match your device memory layout */
  /* These values correspond to the LM3S6965, one of the few devices QEMU can emulate */
  /* FLASH : ORIGIN = 0x00000000, LENGTH = 256K */
  /* RAM : ORIGIN = 0x20000000, LENGTH = 64K */
  /* These values correspond to the STM32F303VCT6, the micrcontroller on the STM32DISCOVERY board */
  FLASH : ORIGIN = 0x08000000, LENGTH = 256K
  RAM : ORIGIN = 0x20000000, LENGTH = 40K
}
```

4. Run the openocd debugger

``` console
$ openocd
```

5. Set a default gdb runner based on the gdb installed on your computer. There are three options as mentioned at the
   top of `.cargo/config`. We'll pick the `arm-none-eabi-gdb` runner.

``` toml
[target.'cfg(all(target_arch = "arm", target_os = "none"))']
# uncomment ONE of these three option to make `cargo run` start a GDB session
# which option to pick depends on your system
runner = "arm-none-eabi-gdb -q -x openocd.gdb"
# runner = "gdb-multiarch -q -x openocd.gdb"
# runner = "gdb -q -x openocd.gdb"
```

6. Run the program with gdb

``` console
$ cargo run
```

7. Continue the gdb debugger (will start with breakpoint on main())

``` console
$ continue
```

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the
work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
