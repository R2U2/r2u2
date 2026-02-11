#!/usr/bin/env bash

# Check for Rust install by checking for bundled `cargo` build system
if ! type cargo > /dev/null; then
    echo "Cannot find 'cargo', install Rust." 1>&2
    exit 1
fi

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
mkdir -p "$SCRIPT_DIR"/deps/

git clone https://github.com/egraphs-good/egglog-experimental.git "$SCRIPT_DIR"/deps/egglog-experimental
cd "$SCRIPT_DIR"/deps/egglog-experimental || { echo "Cannot find egglog-experimental git repo at $SCRIPT_DIR/deps/egglog-experimental" 1>&2 ; exit 2; }
git checkout fb6401e252a4971b6cca808dec8f3c9c650ea552

# Compile egglog:
#  * '--bin': build only build the egglog binary
#  * '--release': in release mode (slower build, faster code)
cargo build --bin egglog-experimental --release
