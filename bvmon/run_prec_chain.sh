
chain=5
nsigs=$((chain + 2))
TIME="gtime"
len=1000000

for ub in 10 100 1000 10000; do
    echo "Generating MLTL formula for UB=$ub"
    python3 gen_prec_chain.py $ub $chain > prec_chain.mltl

    echo "Generating trace for len=$len"
    python3 gen_trace.py $len $nsigs $(echo "scale=5; 3 / $ub" | bc)

    echo "Running r2u2"
    python3 ../compiler/c2po.py prec_chain.mltl > /dev/null
    $TIME -p ../monitors/rust/r2u2_cli/target/release/r2u2_cli run spec.bin trace.r2u2.csv > out.r2u2.log

    echo "Running bvmon"
    python3 ../compiler/c2po.py --no-rewrite --bvmon -c --extops --bvmon-log --bvmon-func --bvmon-nsigs $nsigs --bvmon-word-size 8 prec_chain.mltl > bvmon.c
    gcc -O3 -DOUTPUT -o bvmon bvmon.c
    $TIME -p ./bvmon trace.r2u2.csv > out.bvmon.log

    echo "done"
done

# echo "Generating Prec Chain"
# python3 gen_prec_chain.py 1023 1023 $CHAIN_LEN $WARMUP 10000

# python3 ../compiler/c2po.py prec_chain.mltl > /dev/null
# ../monitors/rust/r2u2_cli/target/release/r2u2_cli run spec.bin prec_chain.csv | ts -i %.s | grep $WARMUP

# python3 ../compiler/c2po.py -c --extops --bvmon --bvmon-log --bvmon-func --bvmon-nsigs $((CHAIN_LEN + 2)) --bvmon-word-size 8 prec_chain.mltl > bvmon.c
# gcc -O3 -o bvmon bvmon.c
# ./bvmon prec_chain.csv 2> stdout.bvmon 1> /dev/null
