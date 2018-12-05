/*=======================================================================================
** File Name: filter_filt.c
**
** Title: Low-pass filter (FIR)
**
** $Author:  J. Schumann
** $Revision: $
** $Date:   2015
**
** Purpose: low-pass filter for R2U2/AT
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
#include "filter_filt.h"

//------------------------------------------------------------
//	initialize LP filter with N elements
//------------------------------------------------------------
void filter_filt_init(int N, double **buf){

int i;

	*buf = (double*)malloc(N*sizeof(double));

	for (i=0; i<N; i++){
		(*buf)[i] = 0.0;
		}
	}

//------------------------------------------------------------
//	free memory
//------------------------------------------------------------
void filter_filt_free(double *buf){

	free(buf);

	}


//------------------------------------------------------------
//	input new data x to filter; execute filter and populate
//	output buffer
//------------------------------------------------------------
double filter_filt_update_data(double x, int N, double *buf){

int i;
double y0 = 0.0;

	// A-part of filter |A| = 1
	// i.e. that's an FIR filter

		//
		// shift buffer
		// and do B-part of filter: |B| = N, B_i = 1;
		//
	for (i=0; i<N-1;i++){
		buf[i]=buf[i+1];
		y0 = y0 + buf[i];
		}
	buf[N-1] = x;
	y0 = y0 + x;

	return y0;

}
