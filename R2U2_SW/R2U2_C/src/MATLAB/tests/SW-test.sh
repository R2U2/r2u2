#!/bin/bash

SW_PATH="$1/R2U2-SW/src/MATLAB/tests"
cd $SW_PATH
octave --silent --eval 'make_r2u2_octave('"'"$2"'"')'
octave --silent --eval 'run_r2u2 '$2' '$3''
