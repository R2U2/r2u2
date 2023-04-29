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

#include "filter_rate.h"

//-----------------------------------------------------------------
//	update rate filter and return current rate
//-----------------------------------------------------------------
r2u2_float filter_rate_update_data(r2u2_float x, r2u2_float *prev)
{
	r2u2_float rate;

	rate = x - *prev;
	*prev = x;

	return rate;
}
