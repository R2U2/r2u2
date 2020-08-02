/*=======================================================================================
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
**=====================================================================================*/

#include <stdlib.h>
#include <stdio.h>
#include "filter_movavg.h"
#include "circbuffer.h"

movAvg_t *filter_movavg_init(uint16_t filter_size) {
	
	int32_t *filt_space = (int32_t *) malloc(sizeof(int32_t) * filter_size);
	circBuf_t *filt_cb = (circBuf_t *) malloc(sizeof(circBuf_t));
	filt_cb->buffer = filt_space;
	filt_cb->head = 0;
	filt_cb->tail = 0;
	filt_cb->maxLen = filter_size;

	movAvg_t *movavg = (movAvg_t *) malloc(sizeof(movAvg_t));
	movavg->pCb = filt_cb;
	movavg->sum = 0;
	movavg->avg = 0;
	movavg->num_of_elements = 0;
	movavg->size = filter_size;

	return movavg;

}
 
//----------------------------------------------------------------
//	update moving avg filter with new data "data"
//----------------------------------------------------------------
void filter_movavg_update_data(movAvg_t *pMovAvg, int32_t data) {

	int32_t old_data;

	// only do pop if data RB is full (real average) (inital fill-up)
	if (pMovAvg->num_of_elements >= pMovAvg->size) {
			//do pop
			circBufPop(pMovAvg->pCb, &old_data);

			
		} else {
			//increase the element counter
			pMovAvg->num_of_elements++;
			old_data = 0;
		}


	//add the new element
	circBufPush(pMovAvg->pCb, data);

	// calculate new sum
	pMovAvg->sum -= old_data;
	pMovAvg->sum += data;
	
	//norm the data and return value
	pMovAvg->avg = (float) pMovAvg->sum / pMovAvg->num_of_elements;

}

//----------------------------------------------------------------
//	get the average value
//----------------------------------------------------------------
float filter_movavg_get(movAvg_t *pMovAvg) {
	return pMovAvg->avg;
}

void filter_movavg_free(movAvg_t *movavg) {
	free(movavg->pCb->buffer);
	free(movavg->pCb);
	free(movavg);
}
