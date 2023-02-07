/*=======================================================================================
** File Name: filter_prognostics.h
**
** Title: header for prognostics filter
**
** $Author:  J. Schumann, Chetan Kulkarni
** $Revision: $
** $Date:   2014
**
** Purpose: 
**
** Limitations, Assumptions, External Events, and Notes:
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**
**=====================================================================================*/

#ifndef FILTER_PROGNOSTICS_H
#define FILTER_PROGNOSTICS_H

#include <stdio.h>
#include <stdlib.h>

#define _CRT_SECURE_NO_WARNINGS


#include "BHM_emxAPI.h"
#include "BHM_types.h"
#include "BHM_emxutil.h"
#include "BHM_rtwutil.h"
#include "BHM_initialize.h"
#include "BHM_terminate.h"
#include "UKFInitialize.h"
#include "computeSOCEstimate.h"
#include "UKFStep.h"
#include "CellConstantInputPredictLookup.h"
#include "computeSigmaPoints.h"

//====================================================================
struct s_prognostics {
	emxArray_real_T *xHat;		// estimated state vector
	emxArray_real_T *zHat;		// estimated output vector
	emxArray_real_T *PHat;		// estimated covariance matrix
	emxArray_real_T *uOld;		// inputs at previous time step
	emxArray_real_T *modelVariance;	// process noise covariance matrix
	emxArray_real_T *sensorVariance;// sensor noise covariance matrix
    
			// model dimensions
	int32_T nx;
	int32_T nu;
	int32_T nz;
	int ii;
	double vUKF;
    	double t;
    
	emxArray_real_T *z;
	emxArray_real_T *u;
	emxArray_real_T *xOld;
	emxArray_real_T *POld;
    
		// set up output arguments
	emxArray_real_T *socMean;
    	double socVariance;
    	int socVariance_Size[2];
	
    		// set up variables for prediction
    	double tP, tMax;
    	emxArray_real_T *EOL;
    	emxArray_real_T *RUL;
    	emxArray_real_T *W;
    
    		// set up input
	emxArray_real_T *U;
	emxArray_real_T *X;
	emxArray_real_T *Wx;

	int isInitialized;

};
//====================================================================
struct s_prognostics* filter_prognostics_init();
void filter_prognostics_free(struct s_prognostics* p);
void filter_prognostics_update(double V, double I, struct s_prognostics* p);
double filter_prognostics_get_RUL_mean(struct s_prognostics* p);
double filter_prognostics_get_SoC_mean(struct s_prognostics* p);
double filter_prognostics_get_RUL_std(struct s_prognostics* p);


#endif
