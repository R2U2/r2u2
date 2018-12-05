#!/bin/bash

##############Configure the following path############
#vivado bin path
PATH=$PATH:/opt/Xilinx/Vivado/2017.2/bin
#project path
PROJ_PATH="/home/pei/git/gitrep/update/SystemHealthManagement/R2U2"
######################################################

RED=`tput setaf 1`
GREEN=`tput setaf 2`
BOLD=$(tput bold)
RESET=`tput sgr0`

#vivado project path
vivado_path="$PROJ_PATH/R2U2-HW/Hardware/hdl/ftMuMonitor/vivado"
#simulation output file path
sim_out_path="$vivado_path/FT_Monitor/FT_Monitor.sim/sim_1/behav"
#path for hardware ft assembly
ftasm_path="$PROJ_PATH/R2U2-HW/Software/ftAssembler"
#path for CPP SW version
cpp_path="$PROJ_PATH/R2U2-SW/MTL"

tests=(test0000 test0023 test0024 test0025 test0026 test0006 test0027 test0028 test0029 test0033 test0030 test0031 test0032)
index=0
index2=1
INPUT="tacas"

chmod +x SW-test.sh
chmod +x HW-test.sh
chmod +x SW-CPP-test.sh
chmod +x $cpp_path/setup.sh
pushd ./
cd $cpp_path
bash setup.sh
popd

for i in ${tests[@]};
do
	bash SW-test.sh $PROJ_PATH $i $INPUT

	cp ./$i/$i.fts $ftasm_path/
	cp _Inputs/$INPUT.dat $ftasm_path/
	cp ./$i/$i.fts $cpp_path/src
	bash HW-test.sh $PATH $PROJ_PATH $i $INPUT
	bash SW-CPP-test.sh $cpp_path $i

    expected="expectedOutput"$index2".txt"

    #Check for Software Emulator Success
    if diff -B _Results/observerOutput.txt ../../../expectedResults/$expected >/dev/null ; then
        SOFTWARESUCCESS[$index]=1
    else 
        SOFTWARESUCCESS[$index]=0
    fi

    #Check for Hardware Success
	if diff -B ../../../expectedResults/$expected $sim_out_path/async_out.txt >/dev/null ; then
        HARDWARESUCCESS[$index]=1
    else 
        HARDWARESUCCESS[$index]=0
    fi 

    #Check for Obj Oriented Software Success
    if diff -B ../../../expectedResults/$expected ../../../MTL/result.txt >/dev/null ; then
        OBJSOFTWARESUCCESS[$index]=1
    else 
        OBJSOFTWARESUCCESS[$index]=0
    fi 

    index=$((index+1))
	index2=$((index2+1))
done



echo "----------------------------------------------------------------------------------------"
echo "                               R2U2 Tests Results                                       "
echo "----------------------------------------------------------------------------------------"
echo "----------------------------------------------------------------------------------------"
echo "|  ${BOLD}Test Name ${RESET} |    ${BOLD}Input Name ${RESET}   |        ${BOLD}C${RESET}        |       ${BOLD}VHDL${RESET}      |        ${BOLD}C++${RESET}      |"
echo "|#############|##################|#################|#################|#################|"

# echo "--------------------------------------------------------------------------------------------------------------------"
# echo "                                                                      R2U2 Tests Results                                                                      "
# echo "--------------------------------------------------------------------------------------------------------------------"
# echo "--------------------------------------------------------------------------------------------------------------------"
# echo "|      ${BOLD}Test Name ${RESET}       |       ${BOLD}Input Name ${RESET}      |       ${BOLD}Hardware Outcome ${RESET}     |     ${BOLD}Software Emulator Outcome ${RESET}     |"
# echo "--------------------------------------------------------------------------------------------------------------------"

index=0
index2=1
while [ $index -lt ${#tests[@]} ]; do
	TEST=$INPUT_$index2
	if [ ${SOFTWARESUCCESS[$index]} -eq 1 ]; then
		COMPARE1=${GREEN}SUCCESS
	else
		COMPARE1=${RED}FAILURE
	fi

	if [ ${HARDWARESUCCESS[$index]} -eq 1 ]; then
		COMPARE2=${GREEN}SUCCESS
	else
		COMPARE2=${RED}FAILURE
	fi

	if [ ${OBJSOFTWARESUCCESS[$index]} -eq 1 ]; then
		COMPARE3=${GREEN}SUCCESS
	else
		COMPARE3=${RED}FAILURE
	fi

    printf '|    %-3s      |      %-9s   |     %-10s  %s   |     %-10s  %s   |     %-10s  %s   |\n' $TEST $INPUT $COMPARE1 ${RESET} $COMPARE2 ${RESET} $COMPARE3${RESET};
    

	index=$((index+1))
	index2=$((index2+1))
    
    echo "|-------------|------------------|-----------------|-----------------|-----------------|"

done