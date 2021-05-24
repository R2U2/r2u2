//============================================================================
// Name        : MTL.cpp
// Author      : Pei Zhang
// Version     : 1.4.0
// Copyright   : Your copyright notice
// Description : Main function for MTL formula verification
//============================================================================
//============================================================================
// Description :
// 1. Assign the sensor number, simulation time stamps;
// 2. Link the sensor to the .log file;
// 3. Write your MLTL formula as a string. For MTL format, see Formula.h;
// 4. Run.
//============================================================================

#include <iostream>
#include <stdio.h>
#include "Observer.h"
#include "Assembly.h"
#include "common.h"

using namespace std;

int main(int argc,char* argv[]) {
	// string asm_file="./input/test.ftasm";
	// string sensor_data_file="./input/sensor.log";
	// string result_file="result.txt";
	if(argc!=4) {
		throw "Argument incorrect\n";
		return -1;
	}
	string asm_file = argv[1], sensor_data_file = argv[2], result_file = argv[3];
	Loader* sensor_loader = new Loader(sensor_data_file.c_str());
	Assembly assm = Assembly(asm_file.c_str());
	Observer** observer = new Observer*[assm.num_of_observer];
	assm.Construct(sensor_loader, observer);
	FILE* pFile;
	pFile = fopen(result_file.c_str(),"w");
	while(sensor_loader->has_next()) {
	//MUST follow the update sequence from bottom layer to top layer (no need to care)
		fprintf(pFile,"----------TIME STEP: %d----------\n",observer[0]->time_stamp);
		for(int n=0;n<assm.num_of_observer;n++) observer[n]->run(pFile);
		observer[0]->time_stamp++;
		fprintf(pFile,"\n");
	}
	fclose (pFile);
	delete sensor_loader;
	delete[] observer;
	return 0;
}
