# R2U2 Core

The Realizable, Reconfigurable, Unobtrusive Unit (R2U2) is a stream-based runtime verification
framework based on Mission-time Linear Temporal Logic (MLTL) designed to monitor safety- or
mission-critical systems with constrained computational resources.

Given a specification and input stream, R2U2 will output a stream of verdicts computing whether the
specification with respect to the input stream. Specifications can be written and compiled using the
Configuration Compiler for Property Organization (C2PO).

# Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
r2u2_core = "0.2.0"
```

# Example Usage

1. Install [r2u2_cli](https://crates.io/crates/r2u2_cli).

    ```bash
    cargo install r2u2_cli
    ```
2. Given the following example.c2po file:
   
        INPUT
            a,b: bool;

        FTSPEC
            F[1,2] (a && b);

    and the following example.csv file:

        # a,b
        0,0
        1,0
        0,1
        1,1
        0,0
        1,0
        0,1
        1,1

    the following command will create a spec.bin file in the current directory:

        r2u2_cli compile example.c2po example.csv

4. Create a Cargo package with R2U2 as a dependency and run as follows in main.rs

    ```
    use r2u2_core;

    use std::fs;

    fn main() {
        let spec_file: Vec<u8> = fs::read("./spec.bin").expect("Error opening specification file");

        let mut monitor = r2u2_core::get_monitor(&spec_file);

        let signal_file: fs::File = fs::File::open("example.csv").expect("Error opening signal CSV file");
        let mut reader = csv::ReaderBuilder::new().trim(csv::Trim::All).has_headers(true).from_reader(signal_file);

        for result in reader.records() {
            let record = &result.expect("Error reading signal values");
            for n in 0..record.len(){
                r2u2_core::load_string_signal(&mut monitor, n, record.get(n).expect("Error reading signal values"));
            }
            if r2u2_core::monitor_step(&mut monitor) {
                for out in r2u2_core::get_output_buffer(&monitor) {
                    println!("{}:{},{}", out.spec_num, out.verdict.time, if out.verdict.truth {"T"} else {"F"} );
                }
            } else {
                println!("Overflow occurred!!!!")
            }
        }

    }
    ```

Microcontroller example also available [here](https://github.com/R2U2/r2u2/tree/rust-develop/monitors/rust/r2u2_cortex_m_example).

## Output

The output of R2U2 is a *verdict stream* with one verdict per line. A verdict includes a **formula
ID**, **timestamp**, and **truth value**. Formula IDs are determined by the order in which they are
defined in the specification file.  Verdicts are *aggregated* so that if R2U2 can determine a range
of values with the same truth at once, only the last time is output.

The following is a stream where formula 0 is true from 0-7 and false from 8-11 and formula 1 is
false from times 0-4:

```
0:7,T
1:4,F
0:11,F
```

# Examples, Specifications, and Traces

Example specifications and traces can be found on our [github page](https://github.com/R2U2/r2u2/tree/rust-develop).

# Documentation

The documentation for R2U2 can be found [here](https://r2u2.github.io/r2u2/). The documentation includes user and developer guides for both R2U2 and C2PO.

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the
work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.