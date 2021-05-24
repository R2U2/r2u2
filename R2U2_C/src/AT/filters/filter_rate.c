/*============================================================================
** File Name: filter_rate.c
**
** Title: Rate filter for R2U2/AT
**
** $Author:  J. Schumann
** $Revision: $
** $Date:   2014
**
** Purpose:  Rate filter to estimate d/dt(X) by
**		(x_t - x_t-1)/delta_T
**
** Functions Defined:
**
** Limitations, Assumptions, External Events, and Notes:
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**
**===========================================================================*/

#include <stdio.h>
#include <stdlib.h>
#include "filter_rate.h"
#include <math.h>

//-----------------------------------------------------------------
//	initialize
//-----------------------------------------------------------------
void filter_rate_init(double *init)
{
	*init = 0;
}

//-----------------------------------------------------------------
//	free memory: NA
//-----------------------------------------------------------------
void filter_rate_free(double *buf){}


//-----------------------------------------------------------------
//	update rate filter and return current rate
//-----------------------------------------------------------------
double filter_rate_update_data(double x, double *prev)
{
	double rate;

	if (isinf(*prev)) {
		rate = 0.0;
	} else {
		rate = x - *prev;
	}

	*prev = x;

	return rate;
}
