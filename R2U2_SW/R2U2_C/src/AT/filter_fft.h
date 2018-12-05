/*=======================================================================================
** File Name: filter_fft.h
**
** Title: header for FFT filter
**
** $Author:  J. Schumann
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

#ifdef FFT_FILTER

#include <stdio.h>
#include <stdlib.h>
#include <fftw3.h>

fftw_plan filter_fft_init(int N, double **buf, fftw_complex **outbuf);

void filter_fft_free(fftw_plan p, double *buf, fftw_complex *outbuf);

void filter_fft_update_data(double x, int N, 
	double *buf, fftw_complex *outbuf, fftw_plan p);

double filter_fft_get(fftw_complex *outbuf, int i);

#endif
