#!/bin/bash

RED=`tput setaf 1`
GREEN=`tput setaf 2`
BOLD=$(tput bold)
RESET=`tput sgr0`

tests=(test0000 test0023 test0024 test0025 test0026 test0006 test0027 test0028 test0029 test0033 test0030 test0031 test0032)
index=0
index2=1
INPUT="tacas"

for i in ${tests[@]};
do

    octave --silent --eval 'make_r2u2_octave('"'"./specs/$i"'"')'
    octave --silent --eval 'run_r2u2 './specs/$i' '$INPUT''


    expected="expectedOutput"$index2".txt"

    #Check for Software Emulator Success
    if diff -B results/observerOutput.txt expectedResults/$expected >/dev/null ; then
        SOFTWARESUCCESS[$index]=1
    else
        SOFTWARESUCCESS[$index]=0
    fi

    index=$((index+1))
    index2=$((index2+1))
done



echo "----------------------------------------------------"
echo "                 R2U2 Tests Results                 "
echo "----------------------------------------------------"
echo "----------------------------------------------------"
echo "|  ${BOLD}Test Name ${RESET} |    ${BOLD}Input Name ${RESET}   |        ${BOLD}C${RESET}        |"
echo "|#############|##################|#################|"

index=0
index2=1
while [ $index -lt ${#tests[@]} ]; do
    TEST=$INPUT_$index2
    if [ ${SOFTWARESUCCESS[$index]} -eq 1 ]; then
        COMPARE1=${GREEN}SUCCESS
    else
        COMPARE1=${RED}FAILURE
    fi

    printf '|    %-3s      |      %-9s   |     %-10s  %s   |\n' $TEST $INPUT $COMPARE1 ${RESET};

    index=$((index+1))
    index2=$((index2+1))

    echo "|-------------|------------------|-----------------|"

done