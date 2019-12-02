/*=======================================================================================
** File Name: filter_fft.c
**
** Title: FFT filter function for R2U2/AT
**
** $Author:  J. Schumann
** $Revision: $
** $Date:   2014
**
** Purpose: FFT filter initialization and update
**
** Functions Defined:
**
** Limitations, Assumptions, External Events, and Notes:
**	NOTE: needs FFTW3 libraries/packages
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**
**=====================================================================================*/


#include <stdio.h>
#include <stdlib.h>
#include <fftw3.h>

#include "filter_fft.h"


//--------------------------------------------------------------------
//	initialize FFT with N elements, buffer buf
//	and output buffer (spectral power) outbuf
//--------------------------------------------------------------------
fftw_plan filter_fft_init(int N, double **buf, fftw_complex **outbuf){

int i;
int nc;

	*buf = (double *)fftw_malloc(N*sizeof(double));
	for (i=0; i<N; i++){
		(*buf)[i] = 0.0;
		}

	nc = ( N / 2 ) + 1;
  	*outbuf = (fftw_complex *)fftw_malloc ( sizeof ( fftw_complex ) * nc );

	return fftw_plan_dft_r2c_1d(N, *buf, *outbuf, FFTW_ESTIMATE);

	}

//--------------------------------------------------------------------
//	free FFT memory and buffers
//--------------------------------------------------------------------
void filter_fft_free(fftw_plan p, double *buf, fftw_complex *outbuf){

	fftw_destroy_plan(p);
	fftw_free(buf);
	fftw_free(outbuf);
	}

//--------------------------------------------------------------------
//	update the FFT with data x, call the FFT and
//	calculate the output buffer
//--------------------------------------------------------------------
void filter_fft_update_data(double x, int N,
	double *buf, fftw_complex *outbuf, fftw_plan p){

int i;

		//
		// shift buffer
		//
	for (i=0; i<N-1;i++){
		buf[i]=buf[i+1];
		}
	buf[N-1] = x;

	fftw_execute(p);

}

//--------------------------------------------------------------------
//	get i-th element (frequency from the filter)
//--------------------------------------------------------------------
double filter_fft_get(fftw_complex *outbuf, int i){

	return outbuf[i][0]*outbuf[i][0] +outbuf[i][1]*outbuf[i][1];

}
