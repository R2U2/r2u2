/*=======================================================================================
** File Name: filter_movavg.h
**
** Title: header for moving average filter
**
** $Author:  P. Moosbrugger
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
#ifndef _MOVAVERAGE_H_
#define _MOVAVERAGE_H_

#include "internals/types.h"

#define MAX_WINDOW_SIZE 5

typedef struct mov_avg {
	r2u2_float buffer[MAX_WINDOW_SIZE];
	r2u2_float sum;
	r2u2_float avg;
    uint8_t head;
	uint8_t num_elems;
} movavg_t;

/* returns a moving average with the window size defined in the
 * instance of pMovAvg (size) for a stream of data that is
 * forwarded with *pData to this function
 * initially the average of the number of included elements is calculated
 * once the windows size has been reached, the average is calculated over the whole window
 * */
r2u2_float filter_movavg_update_data(movavg_t *, r2u2_int,  r2u2_float);
#endif
