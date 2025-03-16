file="$1"
len="$2"
nsigs="$3"
wsize="$4"

# generate the trace
# echo "Generating trace"
# python3 gen_trace.py $len $nsigs $wsize
# echo "Done"

# run r2u2
# python3 ../compiler/c2po.py $file > /dev/null
# time ../monitors/c/build/r2u2 spec.bin trace.r2u2.log > out.r2u2.log
# echo "Done with r2u2"

# run hydra
echo "Running Hydra"
python3 ../compiler/c2po.py --bnf --write-hydra hydra.mtl -c $file
time ../../hydra/hydra hydra.mtl trace.hydra.log > out.hydra.log
echo "Done with hydra"

# run bvmon
echo "Running bvmon"
python3 ../compiler/c2po.py --no-rewrite --bvmon --bvmon-word-size $wsize -c --extops $file > bvmon.c
gcc -DOUTPUT -o bvmon bvmon.c
time ./bvmon trace.bvmon.log > out.bvmon.log
echo "Done with bvmon"

# compare the results
echo "Comparing output"
python3 compare_output.py out.r2u2.log out.hydra.log out.bvmon.log

