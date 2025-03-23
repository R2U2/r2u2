dir="$1"
len="$2"
nsigs="$3"
wsize="$4"

gcc gen_trace.c -o gen_trace -DWORD_SIZE=$wsize -DWORD_TYPE="uint${wsize}_t"

for filename in $dir/*.mltl; do
    echo "Generating trace"
    /usr/bin/time -h ./gen_trace $len $nsigs 1

    echo "Running each tool on $filename"

    # echo "Running r2u2"
    # python3 ../compiler/c2po.py $filename > /dev/null
    # /usr/bin/time -h ../monitors/c/build/r2u2 spec.bin trace.r2u2.log > out.r2u2.log

    echo "Running Hydra"
    python3 ../compiler/c2po.py --bnf --write-hydra hydra.mtl -c $filename
    /usr/bin/time -h ../../hydra/hydra hydra.mtl trace.hydra.log > out.hydra.log

    echo "Running bvmon"
    /usr/bin/time -h python3 ../compiler/c2po.py --no-rewrite --bvmon --bvmon-nsigs $nsigs --bvmon-word-size $wsize -c --extops $filename > bvmon.c
    /usr/bin/time -h gcc -DOUTPUT -o bvmon bvmon.c
    /usr/bin/time -h ./bvmon trace.bvmon.log > out.bvmon.log

    # compare the results
    echo "Comparing output"
    python3 compare_output.py out.r2u2.log out.hydra.log out.bvmon.log
    if [[ $? -ne 0 ]]; then
        exit 1
    fi
done