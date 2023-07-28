
# cd monitors/static
# make clean && make
# cd ../../

# run integration tests...

cd compiler/test
pytest test.py
cd ../../

python compiler/r2u2prep.py --booleanizer examples/agc.mltl examples/agc.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/agc.csv
diff logs/agc.log R2U2.log

python compiler/r2u2prep.py --atomic-checker examples/arb_dataflow.mltl examples/arb_dataflow.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/arb_dataflow.csv
diff logs/arb_dataflow.log R2U2.log

python compiler/r2u2prep.py --atomic-checker examples/atomic_checker.mltl examples/atomic_checker.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/atomic_checker.csv
diff logs/atomic_checker.log R2U2.log

python compiler/r2u2prep.py --booleanizer examples/cav.mltl examples/cav.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/cav.csv
diff logs/cav.log R2U2.log

python compiler/r2u2prep.py --booleanizer examples/set_agg.mltl examples/set_agg.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/set_agg.csv
diff logs/set_agg.log R2U2.log

python compiler/r2u2prep.py --booleanizer examples/sets.mltl examples/sets.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/sets.csv
diff logs/sets.log R2U2.log

python compiler/r2u2prep.py --booleanizer examples/simple.mltl examples/simple.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/simple.csv
diff logs/simple.log R2U2.log

python compiler/r2u2prep.py --booleanizer examples/struct.mltl examples/struct.csv
./monitors/static/build/r2u2 r2u2_spec.bin examples/struct.csv
diff logs/struct.log R2U2.log