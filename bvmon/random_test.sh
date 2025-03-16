file="$1"
len="$2"
nsigs="$3"
wsize="$4"

# generate the trace
python3 gen_trace.py $len $nsigs $wsize

# run r2u2
python3 ../compiler/c2po.py $file > /dev/null
../monitors/c/build/r2u2 spec.bin trace.r2u2.log > out.r2u2.log

# run hydra
python3 ../compiler/c2po.py --bnf --write-hydra hydra.mtl -c $file
../../hydra/hydra hydra.mtl trace.hydra.log > out.hydra.log

# run bvmon
python3 ../compiler/c2po.py --no-rewrite --bvmon --bvmon-word-size $wsize -c --extops $file > bvmon.c
gcc -DOUTPUT -o bvmon bvmon.c
./bvmon trace.bvmon.log > out.bvmon.log

# compare the results
python3 compare_output.py out.r2u2.log out.hydra.log out.bvmon.log

