dir="$1"
len="$2"
nsigs="$3"
wsize="$4"

TIME="gtime"

echo "Generating trace"
python3 gen_trace.py $len $nsigs 0.5

for filename in $dir/*.mltl; do
    echo "Running each tool on $filename"

    echo "Running r2u2"
    python3 ../compiler/c2po.py $filename > /dev/null
    # $TIME -p ../monitors/c/build/r2u2 spec.bin trace.r2u2.csv > out.r2u2.log
    $TIME -p ../monitors/rust/r2u2_cli/target/release/r2u2_cli run spec.bin trace.r2u2.csv > out.r2u2.log

    echo "Running Hydra"
    python3 ../compiler/c2po.py --bnf --write-hydra hydra.mtl -c $filename
    $TIME -p ../../hydra/hydra hydra.mtl trace.hydra.log > out.hydra.log

    echo "Running bvmon"
    $TIME -p python3 ../compiler/c2po.py --no-rewrite --bvmon -c --extops --bvmon-log --bvmon-func --bvmon-nsigs $nsigs --bvmon-word-size $wsize  $filename > bvmon.c
    $TIME -p gcc -O3 -DOUTPUT -o bvmon bvmon.c
    $TIME -p ./bvmon trace.r2u2.csv > out.bvmon.log

    # compare the results
    echo "Comparing output"
    python3 compare_output.py out.r2u2.log out.hydra.log out.bvmon.log
    if [ $? -ne 0 ]; then
        exit 1
    fi
done

# python3 gen_prec_chain.py 

# python3 ../compiler/c2po.py prec_chain.mltl
# ../monitors/c/build/r2u2 spec.bin prec_chain.csv | ts -i %.s > stdout.r2u2

# python3 ../compiler/c2po.py -c --extops --bvmon --bvmon-log --bvmon-func --bvmon-nsigs 6 --bvmon-word-size 8 prec_chain.mltl > bvmon.c
# gcc bvmon.c -o bvmon
# ./bvmon prec_chain.csv 2>&1 | ts -i %.s > stdout.bvmon
