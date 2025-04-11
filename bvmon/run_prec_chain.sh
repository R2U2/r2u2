# 1. Generate precedence chain formula and worst-case trace
# 2. Compile r2u2 with minimum memory required for formula
# 3. Run r2u2/bvmon on formula/trace

chain=5
nsigs=$((chain + 2))
TIME="gtime"
len=5000000

for ub in 10 100 1000 10000; do
    echo "Generating MLTL formula for UB=$ub"
    python3 gen_prec_chain.py $ub $chain > prec_chain.mltl

    echo "Generating trace for len=$len"
    python3 gen_trace.py $len $nsigs $(echo "scale=5; 3 / $ub" | bc)

    echo "Running r2u2"
    python3 ../compiler/c2po.py prec_chain.mltl --quiet
    $TIME -p ../monitors/rust/r2u2_cli/target/release/r2u2_cli run spec.bin trace.r2u2.csv > out.r2u2.log

    echo "Running bvmon"
    python3 ../compiler/c2po.py --no-rewrite --bvmon -c --extops --bvmon-log --bvmon-func --bvmon-nsigs $nsigs --bvmon-word-size 8 prec_chain.mltl > bvmon.c
    gcc -O3 -DOUTPUT -o bvmon bvmon.c
    $TIME -p ./bvmon trace.r2u2.csv > out.bvmon.log

    echo "done"
done
