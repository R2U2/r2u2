#!/usr/bin/env bash

# Check for Rust install by checking for bundeled `cargo` build system
if ! type cargo > /dev/null; then
    echo "Cannot find 'cargo', install Rust." 1>&2
    exit 1
fi

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
mkdir -p "$SCRIPT_DIR"/../deps/
git clone https://github.com/egraphs-good/egglog.git "$SCRIPT_DIR"/deps/egglog
cd "$SCRIPT_DIR"/deps/egglog || { echo "Cannot find egglog git repo at $SCRIPT_DIR/deps/egglog" 1>&2 ; exit 2; }
git checkout v0.4.0

# Compile egglog:
#  * '--bin': build only build the egglog binary
#  * '--release': in release mode (solwer build, faster code)
cargo build --bin egglog --release
