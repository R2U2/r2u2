/*=======================================================================================
** File Name: filter_rate.h
**
** Title: header for rate filter
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
void filter_rate_init(double *init);
void filter_rate_free(void);
double filter_rate_update_data(double x, double *prev);
