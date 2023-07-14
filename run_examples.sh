#!/usr/bin/env bash

printf "\n\nRunning compiler tests\n"
pushd ./compiler/test
pytest test.py
popd

printf "\n\nBuilding monitor\n"
pushd ./monitor
make clean all
popd

printf "\n\nRunning end-to-end tests\n"
pushd ./test
./test_all.sh
popd

printf "\n\nRunning example agc\n"
python ./compiler/r2u2prep.py --booleanizer ./examples/agc.mltl ./examples/agc.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/agc.csv

printf "\n\nRunning example amarb_dataflowples\n"
python ./compiler/r2u2prep.py --atomic-checker ./examples/arb_dataflow.mltl ./examples/arb_dataflow.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/arb_dataflow.csv

printf "\n\nRunning example atomic_checker\n"
python ./compiler/r2u2prep.py --atomic-checker ./examples/atomic_checker.mltl ./examples/atomic_checker.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/atomic_checker.csv

printf "\n\nRunning example cav\n"
python ./compiler/r2u2prep.py --booleanizer ./examples/cav.mltl ./examples/cav.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/cav.csv

printf "\n\nRunning example cse (with CSE off)\n"
python ./compiler/r2u2prep.py --booleanizer --disable-cse ./examples/cse.mltl ./examples/cse.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/cse.csv

printf "\n\nRunning example cse (with CSE enabled\n"
python ./compiler/r2u2prep.py --booleanizer ./examples/cse.mltl ./examples/cse.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/cse.csv

printf "\n\nRunning example set_agg\n"
python ./compiler/r2u2prep.py --booleanizer ./examples/set_agg.mltl ./examples/set_agg.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/set_agg.csv

printf "\n\nRunning example sets\n"
python ./compiler/r2u2prep.py --booleanizer ./examples/sets.mltl ./examples/sets.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/sets.csv

printf "\n\nRunning example simple\n"
python ./compiler/r2u2prep.py --booleanizer ./examples/simple.mltl ./examples/simple.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/simple.csv

printf "\n\nRunning example struct\n"
python ./compiler/r2u2prep.py --booleanizer ./examples/struct.mltl ./examples/struct.csv
./monitor/build/r2u2 r2u2_spec.bin ./examples/struct.csv
