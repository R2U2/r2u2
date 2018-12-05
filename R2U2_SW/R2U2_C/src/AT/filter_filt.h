/*=======================================================================================
** File Name: filter_filt.h
**
** Title: header for FIR filter
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

void filter_filt_init(int N, double **buf);

void filter_filt_free(double *buf);
double filter_filt_update_data(double x, int N, double *buf);

