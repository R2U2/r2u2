#!/bin/bash

# Build the VHDL project and run the simulation
# You can call the script from any location
COMPRUN=$1
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
HWDIR=$"$DIR"/../
WORKDIR=$"$DIR"/../work
TESTBENCHDIR=$"$HWDIR"/ftMuMonitor/sim/testbench

mkdir -p "$WORKDIR"

# Build the dependency
if [ -z "$COMPRUN" ]
then
	find "$HWDIR" -name "*.vhd"  -exec ghdl -i --std=08 --ieee=standard --workdir="$WORKDIR" {} \;
	ghdl -m --std=08 --ieee=standard --workdir="$WORKDIR" ft_mu_monitor
	ghdl -m --std=08 --ieee=standard --workdir="$WORKDIR" tb # add again to solve the 'obsoleted' issue
fi

# Run the testbench
pushd "$PWD"
cd "$TESTBENCHDIR"
ghdl -r --std=08 --ieee=standard --workdir="$WORKDIR" tb
popd