/*=======================================================================================
** File Name: filter_prognostics.c
**
** Title: Prognostics function for R2U2/AT
**
** $Author:  J. Schumann
** $Revision: $
** $Date:   2014
**
** Purpose: This source file contains all necessary functions 
**  to trigger the battery prognostics model (compiled matlab,
**	authors Cheetan Kulkarni etal) and return RUL mean
**
** Functions Defined:
**
** Limitations, Assumptions, External Events, and Notes:
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**
**=====================================================================================*/

#include <stdio.h>
#include <stdlib.h>

#include "filter_prognostics.h"

// #define DEBUG_AT_PROGNOSTICS

//------------------------------------------------------------
//	initialize prognostics filter and compiled code
//------------------------------------------------------------
struct s_prognostics* filter_prognostics_init(){

struct s_prognostics *p;

	p = (struct s_prognostics *)malloc(sizeof(struct s_prognostics));

	// fill individual initialization stuff

	p->nx = 8;
	p->nu = 1;
	p->nz = 2;
    
    	// set up data arrays for UKF Step
	// set up data arrays
	p->xHat = emxCreate_real_T(p->nx,1);
	p->zHat = emxCreate_real_T(p->nz,1);
	p->PHat = emxCreate_real_T(p->nx,p->nx);
	p->uOld = emxCreate_real_T(p->nu,1);
	p->modelVariance = emxCreate_real_T(1,p->nx);
	p->sensorVariance = emxCreate_real_T(1,p->nz);
    
    	// set up variables for the UKFStep function
	p->z = emxCreate_real_T(2,1);             // set up z
	p->u = emxCreate_real_T(1,1);             // set up u
	p->xOld = emxCreate_real_T(8,1);          // set up xOld
	p->POld = emxCreate_real_T(8,8);          // set up POld
    
    	// set up variables for the computeSOC function
	// set up output arguments
	p->socMean = emxCreate_real_T(1,1);
//???    double socVariance;
//???    int socVariance_Size[2];
	
    

    
   	// set up input
	p->U = emxCreate_real_T(1,1);
	
	p->X = emxCreate_real_T(p->nx,2*p->nx+1);
	p->Wx = emxCreate_real_T(1,2*p->nx+1);
    
	// initialize modelVariance
	p->vUKF = 1;
	p->modelVariance->data[0] = 1e-5*p->vUKF;
	p->modelVariance->data[1] = 1e-3*p->vUKF;
	p->modelVariance->data[2] = 1e-3*p->vUKF;
	p->modelVariance->data[3] = 1e-5*p->vUKF;
	p->modelVariance->data[4] = 1e-10*p->vUKF;
	p->modelVariance->data[5] = 1e-10*p->vUKF;
	p->modelVariance->data[6] = 1e-10*p->vUKF;
	p->modelVariance->data[7] = 1e-6*p->vUKF;

	// set up variables for prediction
  	p->EOL = emxCreate_real_T(1,(2*p->nx+1)*p->U->numDimensions);
       	p->RUL = emxCreate_real_T(1,(2*p->nx+1)*p->U->numDimensions);
       	p->W = emxCreate_real_T(1,(2*p->nx+1)*4);
    
	p->isInitialized = 0;

#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: initialized\n");
#endif

	return p;
}

//------------------------------------------------------------
//	free filter memory: TODO
//------------------------------------------------------------
void filter_prognostics_free(struct s_prognostics* p){

	// FREE THE STUFF
	// TODO
#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: free\n");
#endif

}

//------------------------------------------------------------
//	update prognostics model with new data "data"
//	data[0] = timestamp
//	data[1] = battery voltage
//	data[2] = battery current
//	NOTES:
//	* calls compiled matlab model with hardcoded parameters
//	  for a specific battery
//	* update rate is 1Hz
//------------------------------------------------------------
void filter_prognostics_update(double V, double I, struct s_prognostics* p){

int T;
static int newT = 1;
int i;

// newT = data[0];
// I = data[1];
// V = data[2];
T = 25;

	//
	// SCALE to "V" and "A"
V = V/1000.0;
I = I/100.0;

	//
	// can't start prognostics if voltage == 0
	//
if (V < 0.01){
	p->socMean->data[0] = -1.0;
	p->RUL->data[0] = -1.0;
	return;
	}
newT++;

#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: update: %d\n",__LINE__);
OS_printf("R2U2: prognostics: U=%f I=%f newT=%d\n",V,I,newT);
#endif
        
if (!p->isInitialized){
#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: update: %d\n",__LINE__);
#endif
	p->t=newT;
	UKFInitialize(p->t, I, V, T, 
		p->modelVariance, 
		p->xHat, &(p->uOld->data[0]), 
		p->zHat->data, 
		p->PHat);
	p->isInitialized = 1;
#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: update: %d\n",__LINE__);
#endif
	return;
	}


        p->z->data[0] = V;
        p->z->data[1] = T;
        
        p->u->data[0] = I;
        for (i=0; i<p->xHat->size[0]; i++){
            	p->xOld->data[i] = p->xHat->data[i];
        	}
        for (i=0; i< p->PHat->size[0]* p->PHat->size[1]; i++){
            	p->POld->data[i] = p->PHat->data[i];
        	}
        
        // printf("newT %lf\t volt %lf\t curr %lf\n*******\n",newT, voltage, current);
        UKFStep(p->t, newT, p->xOld, p->POld, p->uOld, 
		p->u, p->z, p->modelVariance, p->sensorVariance, 
		p->xHat, p->PHat, p->zHat);

        p->uOld->data[0] = I;
        	// set time
        p->t = newT;
        
        	// compute SOC with Matlab-generated function
        computeSOCEstimate(p->xHat, p->PHat, p->socMean, 
		&(p->socVariance),  p->socVariance_Size);
        
#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: SOC=%lf STD=%lf\n",p->socMean->data[0],p->socVariance);
#endif
        p->tMax = 3600*4.5;
        
        p->tP = newT;
        
        b_computeSigmaPoints(p->xHat, p->PHat, p->X, p->Wx);
        p->U->data[0] = 10; //5-25 is reasonable for this situation

        CellConstantInputPredictLookup(p->tP, p->X, p->Wx, 
		p->U, 'P', p->EOL, p->RUL, p->W);
        
        	// for (ii=0; ii<RUL->numDimensions; ii++ ) {
            	// printf("RUL: %.2f\n",RUL->data[ii]);
        	// }
        
}

//------------------------------------------------------------
//	get RUL mean from filter
//------------------------------------------------------------
double filter_prognostics_get_RUL_mean(struct s_prognostics* p){

#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: get RUL: %d\n",__LINE__);
#endif
	return (p->RUL->data[0]);

}

//------------------------------------------------------------
//	get SoC mean from filter
//------------------------------------------------------------
double filter_prognostics_get_SoC_mean(struct s_prognostics* p){

#ifdef DEBUG_AT_PROGNOSTICS
OS_printf("R2U2: prognostics: get socMean: %d\n",__LINE__);
#endif
	return (p->socMean->data[0]);

}
	
	
//------------------------------------------------------------
//	get RUL std fro filter: TODO
//------------------------------------------------------------
double filter_prognostics_get_RUL_std(struct s_prognostics* p){

	return 0.0001;
}
