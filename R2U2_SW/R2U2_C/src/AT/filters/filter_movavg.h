/*=======================================================================================
** File Name: filter_fft.h
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

#include <stdint.h>

/*
 * Author: Patrick Moosbrugger
 * Usage: instantiate with MOVAVERAGE_DEF(name, size_of_averaging_window)
 */

//#define MOVAVERAGE_DEF(x,y) uint8_t x##_space[y+1]; circBuf_t x##_cb = { x##_space, 0, 0, y+1}; movAvg_t x = {&x##_cb, 0, 0, y};

typedef struct
{
	int32_t *buffer;
	int32_t sum;
	double avg;
  uint16_t head;
	uint16_t num_elems;
	uint16_t size;
} movAvg_t;


/* returns a moving average with the window size defined in the
 * instance of pMovAvg (size) for a stream of data that is
 * forwarded with *pData to this function
 * initially the average of the number of included elements is calculated
 * once the windows size has been reached, the average is calculated over the whole window
 * */
movAvg_t *filter_movavg_init(uint16_t);
void filter_movavg_update_data(movAvg_t *, int32_t);
double filter_movavg_get(movAvg_t *);
void filter_movavg_free(movAvg_t *);
#endif
