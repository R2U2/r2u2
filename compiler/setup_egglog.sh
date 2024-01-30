cargo -V  > /dev/null
if [ $? -ne 0 ]; then
    echo "cargo not installed"
    exit 1
fi

make -v > /dev/null
if [ $? -ne 0 ]; then
    echo "make not installed"
    exit 1
fi

cd c2po/
git clone https://github.com/egraphs-good/egglog.git
cargo install cargo-nextest
make all
cargo build
cd ..