#!/usr/bin/env bash

# Check for Rust install by checking for bundled `cargo` build system
if ! type cargo > /dev/null; then
    echo "Cannot find 'cargo', install Rust." 1>&2
    exit 1
fi

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
DEPS_DIR="$SCRIPT_DIR/../deps"
mkdir -p "$DEPS_DIR"

git clone https://github.com/egraphs-good/egglog-experimental.git "$DEPS_DIR"/egglog-experimental
cd "$DEPS_DIR"/egglog-experimental || { echo "Cannot find egglog-experimental git repo at $DEPS_DIR/deps/egglog-experimental" 1>&2 ; exit 2; }
git checkout 38b3898 # This is the commit of egglog-experimental that is compatible with egglog v2.0.0

# Apply the patch
if [ -f "$SCRIPT_DIR/egglog_experimental.patch" ]; then
    git apply "$SCRIPT_DIR/egglog_experimental.patch"
else
    echo "Warning: egglog_experimental.patch not found at $SCRIPT_DIR/egglog_experimental.patch" 1>&2
fi

# Compile egglog:
#  * '--bin': build only build the egglog binary
#  * '--release': in release mode (slower build, faster code)
cargo build --bin egglog-experimental --release
