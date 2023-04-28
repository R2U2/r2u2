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

#include "filter_movavg.h"

void filter_movavg_init(movavg_t *movavg, uint8_t size) {
    uint8_t i = 0;
    for(i = 0; i < MAX_WINDOW_SIZE; ++i) {
        movavg->buffer[i] = 0;
    }
	movavg->sum = 0;
	movavg->avg = 0;
	movavg->head = 0;
	movavg->num_elems = 0;
    movavg->size = size;
}

//----------------------------------------------------------------
//	update moving avg filter with new data "data"
//----------------------------------------------------------------
r2u2_float filter_movavg_update_data(movavg_t *movavg, r2u2_float new_data) {
	r2u2_float old_data;

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

	movavg->avg = ((r2u2_float)movavg->sum) / ((r2u2_float)movavg->num_elems);
	movavg->head = (movavg->head + 1) % movavg->size;

    return movavg->avg;
}
