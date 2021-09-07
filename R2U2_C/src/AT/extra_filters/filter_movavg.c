/*=============================================================================
** File Name: filter_movavg.c
**
** Title: moving average filter for R2U2/AT
**
** $Author:  P. Moosbrugger
** $Revision: $
** $Date:   2015
**
** Purpose:
** returns a moving average with the window size defined in the
** instance of pMovAvg (size) for a stream of data that is
** forwarded with data to this function
** initially the average of the number of included elements is calculated
** once the windows size has been reached,
** the average is calculated over the whole window
**
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

#include <stdlib.h>
#include <stdio.h>
#include "filter_movavg.h"

movAvg_t *filter_movavg_init(uint16_t filter_size) {

	int32_t *filt_buffer = (int32_t *) malloc(sizeof(int32_t) * filter_size);
	movAvg_t *movavg = (movAvg_t *) malloc(sizeof(movAvg_t));
	movavg->buffer = filt_buffer;
	movavg->sum = 0;
	movavg->avg = 0;
	movavg->head = 0;
	movavg->num_elems = 0;
	movavg->size = filter_size;

	return movavg;

}

//----------------------------------------------------------------
//	update moving avg filter with new data "data"
//----------------------------------------------------------------
void filter_movavg_update_data(movAvg_t *movavg, int32_t new_data) {

	int32_t old_data;

	if(movavg->num_elems == movavg->size) {
		// Buffer is full
		old_data = movavg->buffer[movavg->head];
		movavg->sum -= old_data;
	} else {
		// Buffer is not full
		movavg->num_elems++;
	}

	movavg->buffer[movavg->head] = new_data;
	movavg->sum += new_data;

	movavg->avg = (double)movavg->sum / (double)movavg->num_elems;
	movavg->head = (movavg->head + 1) % movavg->size;

}

//----------------------------------------------------------------
//	get the average value
//----------------------------------------------------------------
double filter_movavg_get(movAvg_t *movavg) {
	return movavg->avg;
}

void filter_movavg_free(movAvg_t *movavg) {
	free(movavg->buffer);
	free(movavg);
}
