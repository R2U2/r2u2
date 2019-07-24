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

int main() {
	string asm_file="./src/test.ftasm";
	Loader* sensor_loader = new Loader("./src/sensor.log");
	Assembly assm = Assembly(asm_file);
	Observer** observer = new Observer*[assm.num_of_observer];
	assm.Construct(sensor_loader, observer);
	FILE* pFile;
	pFile = fopen("result.txt","w");
	int time_step = 0;
	while(sensor_loader->has_next()) {
	//MUST follow the update sequence from bottom layer to top layer (no need to care)
		fprintf(pFile,"----------TIME STEP: %d----------\n",time_step);
		for(int n=0;n<assm.num_of_observer;n++) observer[n]->run(pFile,"PC",time_step);
		time_step++;
		fprintf(pFile,"\n");
	}
	fclose (pFile);
	delete sensor_loader;
	delete[] observer;
	return 0;
}
