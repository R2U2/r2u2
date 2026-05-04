#!/usr/bin/env bash

# Check for Rust install by checking for bundled `cargo` build system
if ! type cargo > /dev/null; then
    echo "Cannot find 'cargo', install Rust." 1>&2
    exit 1
fi

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
DEPS_DIR="$SCRIPT_DIR/../deps"
mkdir -p "$DEPS_DIR"

git clone https://github.com/egraphs-good/egglog.git "$DEPS_DIR"/egglog
cd "$DEPS_DIR"/egglog || { echo "Cannot find egglog git repo at $DEPS_DIR/egglog" 1>&2 ; exit 2; }
git checkout v1.0.0

# Apply the patch
if [ -f "$SCRIPT_DIR/egglog.patch" ]; then
    git apply "$SCRIPT_DIR/egglog.patch"
else
    echo "Warning: egglog.patch not found at $SCRIPT_DIR/egglog.patch" 1>&2
fi

# Compile egglog:
#  * '--bin': build only build the egglog binary
#  * '--release': in release mode (slower build, faster code)
cargo build --bin egglog --release
