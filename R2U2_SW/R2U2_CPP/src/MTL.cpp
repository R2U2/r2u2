//============================================================================
// Name        : MTL.cpp
// Author      : Pei Zhang
// Version     : 1.3.2
// Copyright   : Your copyright notice
// Description : Main function for MTL formula verification
//============================================================================
//============================================================================
// Description :
// 1. Assign the sensor number, simulation time stamps;
// 2. Link the sensor to the .log file;
// 3. Write your MTL formula as a string. For MTL format, see Formula.h;
// 4. Run.
//============================================================================

#include <iostream>
#include <stdio.h>
#include "Observer.h"
#include "Formula.h"
#include "Assembly.h"
#include "common.h"
#define ASM_MODE //comment this line if you are using high level MTL formula

using namespace std;

int main() {
////MTL setup
	string formula="AND{AND{S[0],S[1]},ALW[3,5]{S[0]}}";
	string asm_file="./src/test.ftasm";

	int num_sensor=2;
	int tot_IMU=39;//time length to do the simulation
	Observer** sensor=new Observer*[num_sensor];
	sensor[0]=new Event("./src/alt.log");
	sensor[1]=new Event("./src/pitch.log");
//************************************************************

//Don't touch the following code, the program will automatically establish connections between observers
	#ifndef ASM_MODE
		int num_observer=0;
		for(const char& c:formula) num_observer=(c=='{'||c=='s'||c=='S')?num_observer+1:num_observer;//auto compute the total number of observers required
		cout<<"Number of Observer: "<<num_observer<<endl;
		Observer** observer=new Observer*[num_observer];
		Formula f=Formula(formula,sensor,observer);
		cout<<"MTL Formula: "<<formula<<endl;
	#else
		Assembly assm=Assembly(asm_file);
		Observer** observer=new Observer*[assm.num_of_observer];
		assm.Construct(sensor, observer);
	#endif
		FILE * pFile;
		pFile = fopen ("result.txt","w");
		fprintf(pFile,"**********RESULTS**********\n\n");
		for(int i=0;i<tot_IMU;i++){//simulate at each IMU i, the event happens
		//MUST follow the update sequence from bottom layer to top layer (no need to care)
			fprintf(pFile,"----------TIME STEP: %d----------\n",i);
			#ifndef ASM_MODE
				for(int n=0;n<num_observer;n++) observer[num_observer-n-1]->run(pFile,"NODE");
			#else
				for(int n=0;n<assm.num_of_observer;n++) observer[n]->run(pFile,"PC");
			#endif
			fprintf(pFile,"\n");
		}
		fclose (pFile);
		delete[] sensor;
		delete[] observer;
		return 0;
}
