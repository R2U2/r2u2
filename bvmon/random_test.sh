dir="$1"
len="$2"
nsigs="$3"
wsize="$4"

TIME="gtime"

gcc gen_trace.c -o gen_trace -DWORD_SIZE=$wsize -DWORD_TYPE="uint${wsize}_t"
echo "Generating trace"
$TIME -p ./gen_trace $len $nsigs 2

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
    $TIME -p python3 ../compiler/c2po.py --no-rewrite --bvmon --bvmon-nsigs $nsigs --bvmon-word-size $wsize -c --extops --bvmon-log --bvmon-func $filename > bvmon.c
    $TIME -p gcc -O3 -DOUTPUT -o bvmon bvmon.c
    $TIME -p ./bvmon trace.bvmon.log > out.bvmon.log

    # compare the results
    echo "Comparing output"
    python3 compare_output.py out.r2u2.log out.hydra.log out.bvmon.log
    if [ $? -ne 0 ]; then
        exit 1
    fi
done
