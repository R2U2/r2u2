#!/bin/bash

TEST1=0
TEST2=0
TEST3=0
TEST4=0

INPUT1=0
INPUT2=0
INPUT3=0
INPUT4=0

RED=`tput setaf 1`
GREEN=`tput setaf 2`
BOLD=$(tput bold)

RESET=`tput sgr0`

COUNTER=0

while true; do

    TEST="test"$TEST1$TEST2$TEST3$TEST4
    INPUT="input"$INPUT1$INPUT2$INPUT3$INPUT4
    
    octave --silent --eval 'make_r2u2_octave('"'"$TEST"'"')'
    octave --silent --eval 'run_r2u2 '$TEST' '$INPUT' '    

    
    if diff results/testOutput.txt $TEST/expectedResults/$INPUT/testOutput.txt >/dev/null ; then
        SUCCESS[$COUNTER]=1
    else 
        SUCCESS[$COUNTER]=0
    fi
    
    
    if [ $INPUT4 -eq 3 ]; then
        break
    else
        INPUT4=$((INPUT4+1))
        COUNTER=$((COUNTER+1))
    fi
	

done


INPUT1=0
INPUT2=0
INPUT3=0
INPUT4=0
COUNTER=0


echo "----------------------------------------------------------------------"
echo "                          R2U2 Tests Results                          "
echo "----------------------------------------------------------------------"
echo "----------------------------------------------------------------------"
echo "|      ${BOLD}Test Name       |       ${BOLD}Input Name       |       ${BOLD}Outcome ${RESET}     |"
echo "|######################|########################|####################|"

while [ $INPUT4 -lt 4 ]; do
    INPUT="input"$INPUT1$INPUT2$INPUT3$INPUT4
    if [ ${SUCCESS[$COUNTER]} -eq 1 ]; then 
        echo "|      "$TEST"        |       "$INPUT "       |       ${GREEN}SUCCESS ${RESET}     |"
    else
        echo "|      "$TEST"        |       "$INPUT "       |       ${RED}FAILURE ${RESET}       |"
    fi   
    
    INPUT4=$((INPUT4+1))
    COUNTER=$((COUNTER+1)) 

echo "|----------------------|------------------------|--------------------|"



done







